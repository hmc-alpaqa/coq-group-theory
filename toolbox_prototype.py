import pexpect
import sys
import os
import time

# Python script to try and write functions that would be called in a toolbox prototype.
#       Still very rudimentary.
#       More of a proof of concept, and may need a complete re-work (especially if it
#       is to be used in the browser version).


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

def createVariableEnv(proc, numElem, set):
    '''
    creates a sub-environment with some arbitrary elements
    numElem: number of elements to create, names them using a, b, c, ...
    set: string for the set the elements come from
    '''
    coqStr = "assert (forall ("
    variable = 'a'
    for i in range(numElem):
        coqStr += variable + " "
        variable = chr(ord(variable) + 1)
    
    #TODO: change a<*>b=b<*>a into a generic propositionm, then cancel to replace
    #TODO: also implement admit

    coqStr += ": " + set + "), a <*> b = b <*> a)."
    coqStr += " intros."
    commandString = "(Add () \"" + coqStr + "\")"
    sendCommand(proc, commandString)

def instantiate(proc, hypString, oldVar, newVar):
    '''
    instantiates a statement of one arbitrary variable
    '''

    # determines new instantiated statement
    instHyp = hypString.split(",", 1)[1]
    instHyp = instHyp.replace(oldVar, newVar)

    # asserts and applies general hypothesis
    coqStr = "assert (" + instHyp + "). "
    coqStr += "apply " + hypString.split(":",1)[0] + "."
    commandString = "(Add () \"" + coqStr + "\")"
    sendCommand(proc, commandString)

def reflexive(proc, elem):
    '''
    proves that a given elem is equal to itself
    '''
    coqStr = f"assert ( {elem} = {elem} ). reflexivity. "
    commandString = "(Add () \"" + coqStr + "\")"
    sendCommand(proc, commandString)

def useTool(proc, toolToUse, hypToChange, reverse = False, specElem = "", specElemPos = 0):
    '''
    uses one (equality) hypothesis on another hypothesis
    '''

    coqStr = "rewrite "
    if reverse:
        coqStr += "<- "
    coqStr += f"({toolToUse} {specElem}) in {hypToChange}"
    if specElemPos:
        coqStr += f" at {specElemPos}"
    coqStr += "."
    commandString = "(Add () \"" + coqStr + "\")"
    sendCommand(proc, commandString)


def main():
    try:
        os.remove("log.txt")
    except:
        pass
    proc = pexpect.spawn("sertop -Q .,Defs --print0")
    proc.logfile_send = sys.stdout.buffer
    proc.logfile_read = open("log.txt", "wb")
    proc.expect_exact(
           "\x00(Feedback((doc_id 0)(span_id 1)(route 0)(contents Processed)))\x00")
    
    # Intro/Setup
    sendCommand(proc, "(Add () \"From Defs Require Export group_theory.\")")
    sendCommand(proc, "(Add () \"Lemma boolean_implies_abelian : (forall x : group_theory.G, x<*>x = e) -> (is_abelian group_theory.G). Proof. intros.\")")
    sendCommand(proc, "(Exec 5)")
    sendCommand(proc, "(Query ((sid 5) (pp ((pp_format PpStr)))) Goals)")
    parseAndPrintGoals(open("log.txt").readlines()[-1])
    print("\n")

    # Create first sub-env, with elements a and b
    createVariableEnv(proc, 2, "group_theory.G")
    sendCommand(proc, "(Exec 7)")
    sendCommand(proc, "(Query ((sid 7) (pp ((pp_format PpStr)))) Goals)")
    parseAndPrintGoals(open("log.txt").readlines()[-1])
    print("\n")

    # prove ab^2 = 1.
    instantiate(proc, "H : forall x : group_theory.G, x <*> x = e", "x", "(a <*> b)")
    sendCommand(proc, "(Exec 9)")
    sendCommand(proc, "(Query ((sid 9) (pp ((pp_format PpStr)))) Goals)")
    parseAndPrintGoals(open("log.txt").readlines()[-1])
    print("\n")

    # new statement : ab = ab
    reflexive(proc, "a <*> b")
    sendCommand(proc, "(Exec 11)")
    sendCommand(proc, "(Query ((sid 11) (pp ((pp_format PpStr)))) Goals)")
    parseAndPrintGoals(open("log.txt").readlines()[-1])
    print("\n")

    # rewrite to get ab = (a*1)*b
    useTool(proc, "mult_e", "H1", reverse=True, specElem="a", specElemPos=2)
    sendCommand(proc, "(Exec 12)")
    sendCommand(proc, "(Query ((sid 12) (pp ((pp_format PpStr)))) Goals)")
    parseAndPrintGoals(open("log.txt").readlines()[-1])
    print("\n")

    # replace 1 with ab^2 to get: ab = a(abab)b
    useTool(proc, "H0", "H1", reverse=True)
    sendCommand(proc, "(Exec 13)")
    sendCommand(proc, "(Query ((sid 13) (pp ((pp_format PpStr)))) Goals)")
    parseAndPrintGoals(open("log.txt").readlines()[-1])
    print("\n")

    # associativity to get: ab = (aa)(ba)(bb)
    # TODO: not yet sure how to implement this
    sendCommand(proc, "(Add () \"assert ( a <*> (a <*> b <*> (a <*> b)) <*> b = (a <*> a) <*> (b <*> a) <*> (b <*> b) ). repeat rewrite mult_assoc. auto. rewrite H2 in H1.\" )")
    sendCommand(proc, "(Exec 17)")
    sendCommand(proc, "(Query ((sid 17) (pp ((pp_format PpStr)))) Goals)")
    parseAndPrintGoals(open("log.txt").readlines()[-1])
    print("\n")

    # instantiate to get a^2 = 1, b^2 = 1
    instantiate(proc, "H : forall x : group_theory.G, x <*> x = e", "x", "a")
    instantiate(proc, "H : forall x : group_theory.G, x <*> x = e", "x", "b")
    sendCommand(proc, "(Exec 21)")
    sendCommand(proc, "(Query ((sid 21) (pp ((pp_format PpStr)))) Goals)")
    parseAndPrintGoals(open("log.txt").readlines()[-1])
    print("\n")

    # replace a^2 and b^2 with 1
    useTool(proc, "H3", "H1")
    useTool(proc, "H4", "H1")
    sendCommand(proc, "(Exec 23)")
    sendCommand(proc, "(Query ((sid 23) (pp ((pp_format PpStr)))) Goals)")
    parseAndPrintGoals(open("log.txt").readlines()[-1])
    print("\n")

    # simplify multiplication by 1
    useTool(proc, "mult_e", "H1")
    useTool(proc, "e_mult", "H1")
    sendCommand(proc, "(Exec 25)")
    sendCommand(proc, "(Query ((sid 25) (pp ((pp_format PpStr)))) Goals)")
    parseAndPrintGoals(open("log.txt").readlines()[-1])
    print("\n")

    # TODO: statement to get pulled out of sub-env, also implemented with admit tactic
    sendCommand(proc, "(Add () \" exact H1. \")")
    sendCommand(proc, "(Exec 26)")
    sendCommand(proc, "(Query ((sid 26) (pp ((pp_format PpStr)))) Goals)")
    parseAndPrintGoals(open("log.txt").readlines()[-1])
    print("\n")

    # TODO: not sure how to implement definition unfolding as well
    sendCommand(proc, "(Add () \" unfold is_abelian. exact H0. \")")
    sendCommand(proc, "(Exec 28)")
    sendCommand(proc, "(Query ((sid 28) (pp ((pp_format PpStr)))) Goals)")
    parseAndPrintGoals(open("log.txt").readlines()[-1])
    print("\n")



if __name__ == "__main__":
   main()