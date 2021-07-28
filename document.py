import pexpect
import sys
import os
import time

SLEEP_TIME = 0

def sendCommand(proc, commandString) :
    """ Sends the specified commandString to coq, using the proc. """
    proc.sendline(commandString)
    proc.expect("\(Answer \d+ Completed\)\x00")
    time.sleep(SLEEP_TIME)

def goalCount(str):
    """ Counts how many goals are present after a (Query ... goals) command. """
    goalsStr = str.partition("CoqString\"")[2].partition("\"))))")[0]
    hypGoalsPairs = goalsStr.split("\\n\\n")
    return len(hypGoalsPairs)

def parseAndPrintGoals(str):
    """ Prints the goals and hypothesis nicely after a (Query ... goals) command. """
    goalsStr = str.partition("CoqString\"")[2].partition("\"))))")[0]
    hypGoalsPairs = goalsStr.split("\\n\\n")
    for n in range(len(hypGoalsPairs)):
        (hyp, _, goals ) = hypGoalsPairs[n].partition("\\n============================\\n")
        print("Hypotheses:\n", hyp.replace("\\n", "\n") )
        print("Goals: ", goals)
        print(n+1, "/", len(hypGoalsPairs))
    time.sleep(SLEEP_TIME)

class Document:
    """
    A class to represent a Coq document,
        which utilizes Serapi to change a Coq document.
    Outputs Serapi responses to a log.txt file.

    ...
    Attributes
    ----------
    liveLines : dict
        lines in coq document that are currently "live"
        keys are sid's and values are instances of the Document.Line class
    cancelledLines : dict
        lines in coq document that have been cancelled
        keys are sid's, values are instances of Document.Line class
    currentLine : int
        the furthest line that has been executed
    totalLines : int
        the total number of lines (live + cancelled)
    
    Methods
    -------
    isConsistent : 
        Tests the class to make sure attributes are consistent with coq doc.
    executeAndQueryGoals :
        Executes up to a line, queries and prints goals.
    addStatement :
        Adds new line to end of document.
    removeStatement :
        Removes the last live line, moving it to cancelledLines.
    insertStatement :
        Inserts a new line after the sid provided.
    replaceStatement : 
        Replaces the line at the sid provided.

    Inner Classes
    -------------
    Line :
        stores the information of the line (whether it's been executed, and it's string content)
    """

    def __init__(self):
        """  Creates a new blank coq document. """
        self.liveLines = {}
        self.cancelledLines = {}
        self.currentLine = 1
        self.totalLines = 1

        try:
            os.remove("log")
        except:
            pass

        self.proc = pexpect.spawn("sertop -Q .,Defs --print0")
        # self.proc.logfile_send = sys.stdout.buffer
        self.proc.logfile = open("log", "wb")
        self.proc.expect_exact(
           "\x00(Feedback((doc_id 0)(span_id 1)(route 0)(contents Processed)))\x00")
        
    def __repr__(self):
        """ Prints out all the live lines followed by the cancelled lines. """
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
        ''' Checks that the Coq document and member variables are consistent. '''

        # list of keys should be the same as the range of sid's
        listOfSids = list(self.liveLines.keys()) + list(self.cancelledLines.keys())
        listOfSids.sort()
        if listOfSids != list(range(2, self.totalLines + 1)):
            print("Error: List of keys not the same as range of sid's")
            return False
        
        execSids = [sid for sid in self.liveLines.keys() if sid <= self.currentLine]
        unexecSids = [sid for sid in self.liveLines.keys() if sid > self.currentLine]

        # every live line up to self.currentLine should be executed
        for sid in execSids:
            if self.liveLines[sid].executed != True:
                print("Error: Executed lines listed as unexecuted")
                return False
        
        # every live line after self.currentLine should not be executed
        for sid in unexecSids:
            if self.liveLines[sid].executed != False:
                print("Error: Unexecuted line is listed as executed")
                return False
        
            # unexecuted lines should not have any goals
            sendCommand(self.proc, f"(Query ((sid {sid}) (pp ((pp_format PpStr)))) Goals)")
            if "ObjList()" not in open("log").readlines()[-1]:
                print("Error: unexecuted line has a goal, when it shouldn't")
                return False
        
        # cancelled lines and lines past self.totalLines should not exist
        # leading to "uncaught exception"
        for sid in (list(self.cancelledLines.keys()) + [self.totalLines + 1]):
            sendCommand(self.proc, f"(Query ((sid {sid}) (pp ((pp_format PpStr)))) Ast)")
            # TODO: there may be a better way to check for this
            if "Uncaught exception" not in open("log").readlines()[-1]:
                print("Error: Cancelled lines (or line pas totalLines) exists when it shouldn't")
                return False
        
        # compare strings of each live line
        for sid in self.liveLines.keys():
            sendCommand(self.proc, f"(Query ((sid {sid}) (pp ((pp_format PpStr)))) Ast)")
            responseStr = open("log").readlines()[-1]
            coqStr = responseStr.partition("CoqString")[2].partition("))))")[0]
            
            # remove "" around string if present
            if coqStr[0] == '"' and coqStr[-1] == '"':
                coqStr = coqStr[1:-1]
           
            if (coqStr != self.liveLines[sid].statement):
                print("Line string is inconsistent with coq string")
                return False

        return True
  
    def executeAndQueryGoals(self, sid):
        ''' Executes up to the specified sid, and prints goals at that sid. '''
        sendCommand(self.proc, f"(Exec {sid})")
        
        # Check for errors in trying to execute statement
        serapiReply = open("log").readlines()[-1]
        if "CoqExn" in serapiReply:
            print("The proof assistant couldn't parse this line: ", sid)
            # print(serapiReply)
            print(serapiReply.partition("str\"")[2].partition("\"")[0])
            return 1

        sendCommand(self.proc, f"(Query ((sid {sid}) (pp ((pp_format PpStr)))) Goals)")
        parseAndPrintGoals(open("log").readlines()[-1])

        # Updates executed lines
        for i in self.liveLines.keys():
            if i <= sid:
                self.liveLines[i].executed = True
        
        if self.currentLine < sid:
            self.currentLine = sid

    def addStatement(self, coqStr):
        ''' Adds the corresponding coqStr to the document. Only works one line at a time. '''

        self.totalLines += 1

        commandString = "(Add () \"" + coqStr + "\")"
        sendCommand(self.proc, commandString)

        # check for errors in adding statement
        serapiReply = open("log").readlines()[-1]
        if "CoqExn" in serapiReply:
            print("The proof assistant couldn't parse this statement: ", coqStr)
            # print(serapiReply)
            print(serapiReply.partition("str\"")[2].partition("\"")[0])
            self.totalLines -= 1                # TODO: Find more elegant way to account for this
            return 1
        
        # change coqStr to match what is stored by Coq
        sendCommand(self.proc, f"(Query ((sid {self.totalLines}) (pp ((pp_format PpStr)))) Ast)")
        coqStr = open("log").readlines()[-1]
        coqStr = coqStr.partition("CoqString")[2].partition("))))")[0]
        if coqStr[0] == '"' and coqStr[-1] == '"':                      # remove "" around string if present
            coqStr = coqStr[1:-1]

        self.liveLines[self.totalLines] = self.Line(coqStr)   

    def removeStatement(self):
        ''' 
        Removes the last statement of the live document.
        Returns sid of removed statement.
        '''

        removedSid = max(self.liveLines.keys())
        sendCommand(self.proc, f"(Cancel ({removedSid}))")
        
        #TODO: Catch errors in case cancel is called incorrectly

        # transfer line from live to cancelled dictionary
        self.cancelledLines[removedSid] = self.liveLines.pop(removedSid)

        if self.currentLine >= removedSid:
            self.currentLine = max(self.liveLines.keys())
        
        return removedSid

    def insertStatement(self, sid, coqStr):
        '''
        Inserts the coqStr statement after the provided sid.
        If sid is invalid, does nothing.
        '''

        if sid == max(self.liveLines.keys()):
            self.addStatement(coqStr)
            return
        elif sid not in self.liveLines.keys():
            print("invalid sid")
            return 1
        
        # Remove every line past desired sid, and save the removed sids
        remSids = []
        while max(self.liveLines.keys()) > sid:
            remSids = [self.removeStatement()] + remSids

        # Add in new coqStr and removedSids
        self.addStatement(coqStr)
        for i in remSids:
            self.addStatement(self.cancelledLines[i].statement)
    
    def replaceStatement(self, sid, coqStr):
        '''
        Replaces the statement and the sid with the new coqStr.
        If sid is invalid, does nothing.
        '''

        if sid not in self.liveLines.keys():
            print("Tried to replace statement at invalid sid")
            return
        
        # Remove every line past desired sid and save the removed sids
        remSids = []
        while max(self.liveLines.keys()) > sid:
            remSids = [self.removeStatement()] + remSids
        
        # Remove statement at sid, add in new and removed statements
        self.removeStatement()
        self.addStatement(coqStr)
        for i in remSids:
            self.addStatement(self.cancelledLines[i].statement)

    class Line:
        """
        A class that stores information about a Line in a coq document.

        ...
        Attributes
        ----------
        statement : str
            the text of the Line
        executed : bool
            whether the Line has been executed
        """

        def __init__(self, coqStr):
            """ Creates a new line with the provided coqStr. """
            self.statement = coqStr
            self.executed = False



def testing():
    """ Tests how the calls might be made for the toolbox prototype. """
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
    print("Doc consistent:", doc.isConsistent())
    
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

def testing2():
    """ For testing error catching. """
    doc = Document()
    print(doc)

    doc.addStatement("From Defs Require Export group_theory.") # starts here with sid 2
    doc.addStatement("Lemma boolean_implies_abelian : (forall x : group_theory.G, x<*>x = e) -> (is_abelian group_theory.G).")
    doc.addStatement("Proof.")
    doc.addStatement("intros.")         # sid 5

    doc.addStatement("assert (forall (a b : group_theory.G), Prop).")
    doc.addStatement("intros.")         # sid 7
    doc.addStatement("admit.")          # sid 8

    doc.removeStatement()
    doc.executeAndQueryGoals(7)
    print("\n\n Current State of Document: \n", doc)
    print("Doc consistent:", doc.isConsistent())

    # syntax to add is incorrect
    doc.addStatement("assert b = b.")

    # trying to introduce new variable
    doc.addStatement("assert (c = b).")
    doc.executeAndQueryGoals(9)
    print("\n\n Current State of Document: \n", doc)
    print("Doc consistent:", doc.isConsistent())

    # incorrect application of tactic
    doc.removeStatement()
    doc.addStatement("apply H.")
    doc.executeAndQueryGoals(10)
    print("\n\n Current State of Document: \n", doc)
    print("Doc consistent:", doc.isConsistent())

    # TODO: Try to find more possible errors?

if  __name__ == "__main__":
    testing2()
