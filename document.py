import pexpect
import sys
import os
import time

SLEEP_TIME = 0

def sendCommand(proc, commandString) :
    proc.sendline(commandString)
    proc.expect("\(Answer \d+ Completed\)\x00")
    time.sleep(SLEEP_TIME)

def parseAndPrintGoals(str):
    goalsStr = str.partition("CoqString\"")[2].partition("\"))))")[0]
    hypGoalsPairs = goalsStr.split("\\n\\n")
    for n in range(len(hypGoalsPairs)):
        (hyp, _, goals ) = hypGoalsPairs[n].partition("\\n============================\\n")
        print("Hypotheses:\n", hyp.replace("\\n", "\n") )
        print("Goals: ", goals)
        print(n+1, "/", len(hypGoalsPairs))
    time.sleep(SLEEP_TIME)

class Document:

    def __init__(self):
        self.liveLines = {}
        self.cancelledLines = {}
        self.currentLine = 1
        self.totalLines = 1

        try:
            os.remove("log")
        except:
            pass
        self.proc = pexpect.spawn("sertop -Q .,Defs --print0")
        #self.proc.logfile_send = sys.stdout.buffer
        self.proc.logfile = open("log", "wb")
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
        for sid in execSids:
            if self.liveLines[sid].executed != True:
                print("Test 2 Failed")
                return False
        
        # every live line after self.currentLine should not be executed
        for sid in unexecSids:
            if self.liveLines[sid].executed != False:
                print("Test 3 Failed")
                return False
        
            # unexecuted lines should not have any goals
            sendCommand(self.proc, f"(Query ((sid {sid}) (pp ((pp_format PpStr)))) Goals)")
            if "ObjList()" not in open("log").readlines()[-1]:
                print("Test 4 Failed")
                return False
        
        # cancelled lines and lines past self.totalLines should not exist
        # leading to "uncaught exception"
        for sid in (list(self.cancelledLines.keys()) + [self.totalLines + 1]):
            sendCommand(self.proc, f"(Query ((sid {sid}) (pp ((pp_format PpStr)))) Ast)")
            # TODO: there may be a better way to check for this
            if "Uncaught exception" not in open("log").readlines()[-1]:
                print("Test 5 Failed")
                return False
        
        # compare strings of each live line
        for sid in self.liveLines.keys():
            sendCommand(self.proc, f"(Query ((sid {sid}) (pp ((pp_format PpStr)))) Ast)")
            responseStr = open("log.txt").readlines()[-1]
            coqStr = responseStr.partition("CoqString")[2].partition("))))")[0]
            
            # remove "" around string if present
            if coqStr[0] == '"' and coqStr[-1] == '"':
                coqStr = coqStr[1:-1]
           
            if (coqStr != self.liveLines[sid].statement):
                print("Test 6 Failed")
                return False

        return True
  
    def executeAndQueryGoals(self, sid):
        ''' executes up to the specified sid, and returns goals at that sid '''
        sendCommand(self.proc, f"(Exec {sid})")
        sendCommand(self.proc, f"(Query ((sid {sid}) (pp ((pp_format PpStr)))) Goals)")
        parseAndPrintGoals(open("log").readlines()[-1])

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
        coqStr = coqStr.partition("CoqString")[2].partition("))))")[0]

        # remove "" around string if present
        if coqStr[0] == '"' and coqStr[-1] == '"':
            coqStr = coqStr[1:-1]

        self.liveLines[self.totalLines] = self.Line(coqStr)   

    def removeStatement(self):
        ''' 
        removes the last statement of the live document 
        returns sid of removed statement
        '''

        removedSid = max(self.liveLines.keys())
        sendCommand(self.proc, f"(Cancel ({removedSid}))")

        # transfer line from live to cancelled dictionary
        self.cancelledLines[removedSid] = self.liveLines.pop(removedSid)

        if self.currentLine >= removedSid:
            self.currentLine = max(self.liveLines.keys())
        
        return removedSid

    def insertStatement(self, sid, coqStr):
        '''
        inserts the coqStr statement after the provided sid
        if sid is invalid, does nothing
        '''

        if sid == max(self.liveLines.keys()):
            self.addStatement(coqStr)
            print("Added to end automatically")
            return
        elif sid not in self.liveLines.keys():
            print("invalid sid")
            return
        
        # Remove every line past desired sid, and save the removed sids to front of list
        remSids = []
        while max(self.liveLines.keys()) > sid:
            remSids = [self.removeStatement()] + remSids

        # Add in new coqStr
        self.addStatement(coqStr)

        # Add back in the removed sids
        for i in remSids:
            self.addStatement(self.cancelledLines[i].statement)
    
    def replaceStatement(self, sid, coqStr):
        '''
        replaces the statement and the sid with the new coqStr
        if sid is invalid, does nothing
        '''

        if sid not in self.liveLines.keys():
            print("Tried to replace statement at invalid sid")
            return
        
        # Remove every line up past the desired sid and save the removed sids to front of list
        remSids = []
        while max(self.liveLines.keys()) > sid:
            remSids = [self.removeStatement()] + remSids
        
        # Remove current sid, but do not save
        self.removeStatement()
        
        # Add in new coqStr
        self.addStatement(coqStr)

        # add back in extra sids
        for i in remSids:
            self.addStatement(self.cancelledLines[i].statement)
        


    class Line:
        def __init__(self, coqStr):
            self.statement = coqStr
            self.executed = False



def testing():
    doc = Document()
    print(doc)

    doc.addStatement("From Defs Require Export group_theory.") # starts here with sid 2
    doc.addStatement("Lemma boolean_implies_abelian : (forall x : group_theory.G, x<*>x = e) -> (is_abelian group_theory.G).")
    doc.addStatement("Proof.")
    doc.addStatement("intros.")         # sid 5

    doc.addStatement("assert (forall (a b : group_theory.G), Prop).")
    doc.addStatement("intros.")         # sid 7
    doc.addStatement("admit.")          # sid 8

    doc.executeAndQueryGoals(5)
    print("\n\n Current State of Document: \n", doc)

    doc.insertStatement(7, "assert ( (a <*> b) <*> (a <*> b) = e).") # sid 9
    doc.insertStatement(9, "apply H.")                               # sid 11
    doc.insertStatement(11, "assert ( a <*> b = a <*> b ).")
    doc.insertStatement(13, "reflexivity.")
    doc.insertStatement(15, "rewrite <- (mult_e a) in H1 at 2.")
    doc.insertStatement(17, "rewrite <- H0 in H1.") # sid 19

    doc.insertStatement(19, "assert ( a <*> (a <*> b <*> (a <*> b)) <*> b = (a <*> a) <*> (b <*> a) <*> (b <*> b) ).")
    doc.insertStatement(21, "repeat rewrite mult_assoc.")
    doc.insertStatement(23, "auto.")
    doc.insertStatement(25, "rewrite H2 in H1.") # sid 27

    doc.insertStatement(27, "assert (a <*> a = e).")
    doc.insertStatement(29, "apply H.")
    doc.insertStatement(31, "assert (b <*> b = e).")
    doc.insertStatement(33, "apply H.")
    
    doc.insertStatement(35, "rewrite H3 in H1.")
    doc.insertStatement(37, "rewrite H4 in H1.")
    doc.insertStatement(39, "rewrite mult_e in H1.")
    doc.insertStatement(41, "rewrite e_mult in H1.")

    doc.executeAndQueryGoals(43)
    print("\n\n Current State of Document: \n", doc)

    doc.replaceStatement(6, "assert (forall (a b : group_theory.G), a <*> b = b <*> a).")
    doc.replaceStatement(65, "exact H1.")

    doc.executeAndQueryGoals(66)
    print("\n\n Current State of Document: \n", doc)

    doc.addStatement("unfold is_abelian.")
    doc.addStatement("exact H0.")

    doc.executeAndQueryGoals(68)
    print("\n\n Current State of Document: \n", doc)
    print("Doc consistent:", doc.isConsistent())
    



# if  __name__ == "__main__":
#     testing()


    
    