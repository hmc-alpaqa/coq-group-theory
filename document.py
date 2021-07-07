import pexpect
import sys
import os
import time

def sendCommand(proc, commandString) :
    proc.sendline(commandString)
    proc.expect("\(Answer \d+ Completed\)\x00")
    time.sleep(0.1)

def parseAndPrintGoals(str):
    goalsStr = str.partition("CoqString\"\\n ")[2].partition("\"))))")[0]
    hypGoalsPairs = goalsStr.split("\\n\\n")
    for n in range(len(hypGoalsPairs)):
        (hyp, _, goals ) = hypGoalsPairs[n].partition("\\n============================\\n")
        print("Hypotheses:\n", hyp.replace("\\n", "\n") )
        print("Goals: ", goals)
        print(n+1, "/", len(hypGoalsPairs))
    time.sleep(0.1)

class Document:

    def __init__(self):
        self.liveLines = {}
        self.cancelledLines = {}
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
        
    def __repr__(self):
        res = "Live Doc: \n"

        for sid in self.liveLines.keys():
            res += f"   Line {sid}:"
            if self.liveLines[sid].executed == True:
                res += " --  Exec'd --"
            res += " " + self.liveLines[sid].statement + "\n"
        
        res += "Cancelled Lines: \n"
        for sid in self.cancelledLines.keys():
            res += f"   Line {sid}:"
            if self.cancelledLines[sid].executed == True:
                res += " --  Exec'd --"
            res += " " + self.cancelledLines[sid].statement + "\n"

        return res
    
    def isConsistent(self):
        ''' checks that the coq document and member variables are consistent '''

        # list of keys should be the same as the range of sid's
        listOfSids = list(self.liveLines.keys()) + list(self.cancelledLines.keys())
        listOfSids.sort()
        if listOfSids != list(range(2, self.totalLines + 1)):
            print("Test 1 Failed")
            return False
        
        execSids = [sid for sid in self.liveLines.keys() if sid <= self.currentLine]
        unexecSids = [sid for sid in self.liveLines.keys() if sid > self.currentLine]

        # every live line upto self.currentLine should be executed
        # and every live line after self.currentLine should not be executed
        for sid in execSids:
            if self.liveLines[sid].executed != True:
                print("Test 2 Failed")
                return False
        for sid in unexecSids:
            if self.liveLines[sid].executed != False:
                print("Test 3 Failed")
                return False
        
            # unexecuted lines should not have any goals
            sendCommand(self.proc, f"(Query ((sid {sid}) (pp ((pp_format PpStr)))) Goals)")
            if "ObjList()" not in open("log.txt").readlines()[-1]:
                print("Test 4 Failed")
                return False
        
        # cancelled lines and lines past self.totalLines should not exist
        # leading to "uncaught exception"
        for sid in (list(self.cancelledLines.keys()) + [self.totalLines + 1]):
            sendCommand(self.proc, f"(Query ((sid {sid}) (pp ((pp_format PpStr)))) Ast)")
            # TODO: there may be a better way to check for this
            if "Uncaught exception" not in open("log.txt").readlines()[-1]:
                print("Test 5 Failed")
                return False
        
        # compare strings of each live line
        for sid in self.liveLines.keys():
            sendCommand(self.proc, f"(Query ((sid {sid}) (pp ((pp_format PpStr)))) Ast)")
            responseStr = open("log.txt").readlines()[-1]
            coqStr = responseStr.partition("CoqString\"")[2].partition("\"))))")[0]
            if (coqStr != self.liveLines[sid].statement):
                print("Test 6 Failed")
                return False

        return True
  
    def executeAndQueryGoals(self, sid):
        ''' executes up to the specified sid, and returns goals at that sid '''
        sendCommand(self.proc, f"(Exec {sid})")
        sendCommand(self.proc, f"(Query ((sid {sid}) (pp ((pp_format PpStr)))) Goals)")
        parseAndPrintGoals(open("log.txt").readlines()[-1])

        for i in self.liveLines.keys():
            if i <= sid:
                self.liveLines[i].executed = True
        
        if self.currentLine < sid:
            self.currentLine = sid

    def addStatement(self, coqStr):
        ''' adds the corresponding coqStr to the document, only one line at a time '''

        self.totalLines += 1

        commandString = "(Add () \"" + coqStr + "\")"
        sendCommand(self.proc, commandString)

        # change string to match what is stored by Coq
        sendCommand(self.proc, f"(Query ((sid {self.totalLines}) (pp ((pp_format PpStr)))) Ast)")
        coqStr = open("log.txt").readlines()[-1]
        coqStr = coqStr.partition("CoqString\"")[2].partition("\"))))")[0]

        self.liveLines[self.totalLines] = self.Line(coqStr)   

    def removeStatement(self):
        ''' removes the last statement of the document, returns the line removed as a string '''

        removedSid = max(self.liveLines.keys())
        sendCommand(self.proc, f"(Cancel ({removedSid}))")

        # transfer line to cancelled dictionary
        self.cancelledLines[removedSid] = self.liveLines.pop(removedSid)

        if self.currentLine >= removedSid:
            self.currentLine = max(self.liveLines.keys())

    def insertStatement(self, sid, coqStr):
        '''
        inserts the coqStr statement after the provided sid
        if sid is too large, string is just added to the end of the doc
        if sid is otherwise invalid, does nothing
        '''

        # TODO: fix to account for cancelled dictionary

        print("\n\n\n Starting to insert:", coqStr)
        print("Total Lines:", self.totalLines)
        print("Insert After:", sid)

        if sid >= self.totalLines:
            self.addStatement(coqStr)
            print("Added to end automatically")
            return
        elif sid not in self.contents.keys():
            print("invalid sid")
            return
        
        print("Valid sid, continuing...")
        

        remStatements = []
        for i in range(self.totalLines, sid, -1):
            remStatements.append(self.removeStatement())
        print("Removed Statements: ", remStatements)
        print("Doc after removing later statements")
        print(self)
        print(self.isConsistent(), "consistency")
        
        
        self.addStatement(coqStr)

        print("Doc with added statements")
        print(self)

        while remStatements:
            self.addStatement(remStatements.pop())
        
        print("Completed doc")
        print(self)

        print("Finished! \n\n\n")
        


    class Line:
        def __init__(self, coqStr):
            self.statement = coqStr
            self.executed = False



def testing():
    doc = Document()
    print(doc.isConsistent(), "consistency")
    print(doc)

    doc.addStatement("From Defs Require Export group_theory.") # starts here with sid 2
    doc.addStatement("Lemma boolean_implies_abelian : (forall x : group_theory.G, x<*>x = e) -> (is_abelian group_theory.G).")
    doc.addStatement("Proof.")
    doc.addStatement("intros.")         # sid 5

    doc.executeAndQueryGoals(5)
    print(doc.isConsistent(), "consistency")
    print(doc)

    doc.addStatement("assert (forall (a b : group_theory.G), Prop).")
    doc.addStatement("intros.")         # sid 7
    doc.addStatement("admit.")          # sid 8

    doc.executeAndQueryGoals(8)
    print(doc.isConsistent(), "consistency")
    print(doc)

    doc.removeStatement()

    doc.addStatement("assert ( (a <*> b) <*> (a <*> b) = e).")
    doc.addStatement("apply H.")

    doc.executeAndQueryGoals(10)
    print(doc.isConsistent(), "consistency")
    print(doc)

    '''
    sendCommand(doc.proc, "(Query ((sid 7) (pp ((pp_format PpStr)))) Ast)")
    sendCommand(doc.proc, "(Query ((sid 8) (pp ((pp_format PpStr)))) Ast)")
    sendCommand(doc.proc, "(Query ((sid 9) (pp ((pp_format PpStr)))) Ast)")
    
    doc.executeAndQueryGoals(7)
    doc.executeAndQueryGoals(8)
    doc.executeAndQueryGoals(9)
    '''




testing()

    
    