import pexpect
import sys
import os
import time

def sendCommand(proc, commandString) :
    proc.sendline(commandString)
    proc.expect("\(Answer \d+ Completed\)\x00")
    time.sleep(0.1)

def parseAndPrintGoals(str):
    goalsStr = str.partition("CoqString\"")[2].partition("\"))))")[0]
    (hyp, _, goals ) = goalsStr.partition("\\n============================\\n")
    print("Hypotheses:   ", hyp.replace("\\n", "\n") )
    print("Goals: \n   ", goals.replace("\\n                             ", " "))
    time.sleep(0.1)

class Document:

    def __init__(self):
        self.contents = {}
        self.currentLine = 1
        self.totalLines = 1

        try:
            os.remove("log.txt")
        except:
            pass
        self.proc = pexpect.spawn("sertop -Q .,Defs --print0")
        self.proc.logfile_send = sys.stdout.buffer
        self.proc.logfile_read = open("log.txt", "wb")
        self.proc.expect_exact(
           "\x00(Feedback((doc_id 0)(span_id 1)(route 0)(contents Processed)))\x00")
    
    def isConsistent(self):

        # every line upto self.currentLine should be executed
        for sid in range(2, self.currentLine + 1):
            if self.contents[sid].executed != True:
                return False

        # every line past self.currentLine should not be executed
        for sid in range(self.currentLine + 1, self.totalLines + 1):
            if self.contents[sid].executed != False:
                return False
        
        # unexecuted lines should not have any goals
        sendCommand(self.proc, f"(Query ((sid {self.currentLine + 1}) (pp ((pp_format PpStr)))) Goals)")
        if "ObjList()" not in open("log.txt").readlines()[-1]:
            return False
        
        # lines past self.totalLines should not exist, leading to "uncaught exception"
        sendCommand(self.proc, f"(Query ((sid {self.totalLines + 1}) (pp ((pp_format PpStr)))) Ast)")
        # TODO: there may be a better way to check for this
        if "Uncaught exception" not in open("log.txt").readlines()[-1]:
            return False
        
        # compare strings of each line
        '''
        for sid in range(2, self.totalLines + 1):
            sendCommand(self.proc, f"(Query ((sid {sid}) (pp ((pp_format PpStr)))) Ast)")
            responseStr = open("log.txt").readlines()[-1]
            coqStr = responseStr.partition("CoqString")[2].partition("))))")[0]
            print(coqStr)
            print(self.contents[sid].statement)
            print("\n")
        '''
            # TODO: not sure how to compare the strings, discrepancy in parenthesis

        return True

  
    def addStatement(self, coqStr):
        commandString = "(Add () \"" + coqStr + "\")"
        sendCommand(self.proc, commandString)

        self.totalLines += 1
        self.contents[self.totalLines] = self.Line(coqStr)
    
    def executeAndQueryGoals(self, sid):
        sendCommand(self.proc, f"(Exec {sid})")
        sendCommand(self.proc, f"(Query ((sid {sid}) (pp ((pp_format PpStr)))) Goals)")
        parseAndPrintGoals(open("log.txt").readlines()[-1])

        for i in range(2, sid+1):
            self.contents[i].executed = True
        
        if self.currentLine < sid:
            self.currentLine = sid

    
    class Line:
        def __init__(self, coqStr):
            self.statement = coqStr
            self.executed = False



def testing():
    doc = Document()
    print(doc.isConsistent())

    doc.addStatement("From Defs Require Export group_theory.")
    doc.addStatement("Lemma boolean_implies_abelian : (forall x : group_theory.G, x<*>x = e) -> (is_abelian group_theory.G).")
    doc.addStatement("Proof.")
    doc.addStatement("intros.")

    doc.addStatement("assert (forall (a b : group_theory.G), a <*> b = b <*> a).")
    doc.addStatement("intros.")   # sid 7
    doc.addStatement("assert ( (a <*> b) <*> (a <*> b) = e).")
    doc.addStatement("apply H.")

    doc.executeAndQueryGoals(7)
    print("Current total lines is: ", doc.totalLines)
    print("Current executed lines is:", doc.currentLine)

    print(doc.isConsistent())

    '''
    sendCommand(doc.proc, "(Query ((sid 7) (pp ((pp_format PpStr)))) Goals)")
    sendCommand(doc.proc, "(Query ((sid 8) (pp ((pp_format PpStr)))) Goals)")
    sendCommand(doc.proc, "(Exec 8)")
    sendCommand(doc.proc, "(Query ((sid 8) (pp ((pp_format PpStr)))) Goals)")
    sendCommand(doc.proc, "(Query ((sid 10) (pp ((pp_format PpStr)))) Ast)")

    sendCommand(doc.proc, "(Exec 9)")
    sendCommand(doc.proc, "(Query ((sid 9) (pp ((pp_format PpStr)))) Ast)")
    sendCommand(doc.proc, "(Query ((sid 9) (pp ((pp_format PpStr)))) Goals)")
    sendCommand(doc.proc, "(Exec 7)")
    sendCommand(doc.proc, "(Query ((sid 9) (pp ((pp_format PpStr)))) Ast)")
    sendCommand(doc.proc, "(Query ((sid 9) (pp ((pp_format PpStr)))) Goals)")
    '''


testing()

    
    