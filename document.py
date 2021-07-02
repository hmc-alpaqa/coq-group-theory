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
    (hyp, _, goals ) = goalsStr.partition("\\n============================\\n")
    print("Hypotheses:\n", hyp.replace("\\n", "\n") )
    print("Goals: ", goals)
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
    
  
    def addStatement(self, coqStr):
        commandString = "(Add () \"" + coqStr + "\")"
        sendCommand(self.proc, commandString)

        self.totalLines += 1
        self.contents[self.totalLines] = self.Line(coqStr)
    
    class Line:
        def __init__(self, coqStr):
            self.statement = coqStr
            self.executed = False



def testing():
    doc = Document()
    doc.addStatement("From Defs Require Export group_theory.")
    sendCommand(doc.proc, "(Exec 2)")
    sendCommand(doc.proc, "(Query ((sid 2) (pp ((pp_format PpStr)))) Ast)")
    print(doc.contents[2].statement)    # SID 2 is export
    print("\n")

    doc.addStatement("Lemma boolean_implies_abelian : (forall x : group_theory.G, x<*>x = e) -> (is_abelian group_theory.G).")
    sendCommand(doc.proc, "(Exec 3)")
    sendCommand(doc.proc, "(Query ((sid 3) (pp ((pp_format PpStr)))) Ast)")
    print(doc.contents[3].statement)    # SID 3 is lemma
    sendCommand(doc.proc, "(Query ((sid 2) (pp ((pp_format PpStr)))) Ast)")

testing()

    
    