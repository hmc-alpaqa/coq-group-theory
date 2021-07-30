import pexpect
import sys
import os
import time

# Python script originally used to make sure python and serapi can interact.
#       Used to make sure we can make serapi calls using python.
#       File is mostly oudated and probably no longer necessary.
# For a more complete version/implementation, see document.py and cli.py.


def sendCommand(proc, commandString) :
    proc.sendline(commandString)
    proc.expect("\(Answer \d+ Completed\)\x00")
    time.sleep(0.75)

def parseAndPrintGoals(str):
    goalsStr = str.partition("CoqString\"\\n ")[2].partition("\"))))")[0]
    (hyp, _, goals ) = goalsStr.partition("\\n============================\\n")
    print("Hypotheses:\n", hyp.replace("\\n", "\n") )
    print("Goals: ", goals)
    time.sleep(0.75)
    
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
    sendCommand(proc, "(ReadFile  \"group_theory.v\")")
    sendCommand(proc,"(Add () \"Lemma boolean_implies_abelian : (forall x : group_theory.G, x<*>x = e) -> (forall (a b : group_theory.G), a<*>b = b<*>a). Proof. intros.\")")
    sendCommand(proc, "(Exec 101)")
    sendCommand(proc, "(Query ((sid 5) (pp ((pp_format PpStr)))) Goals)")
    parseAndPrintGoals(open("log.txt").readlines()[-1])
    sendCommand(proc, "(Add () \"assert ( (a <*> b) <*> (a <*> b) = e). apply H.\")")
    sendCommand(proc, "(Exec 103)")
    sendCommand(proc, "(Query ((sid 7) (pp ((pp_format PpStr)))) Goals)")
    parseAndPrintGoals(open("log.txt").readlines()[-1])
    sendCommand(proc, "(Add () \"assert ( (a <*> b) = (a <*> b) ). reflexivity.\")")
    sendCommand(proc, "(Exec 105)")
    sendCommand(proc, "(Query ((sid 9) (pp ((pp_format PpStr)))) Goals)")
    parseAndPrintGoals(open("log.txt").readlines()[-1])
    sendCommand(proc, "(Add () \"  rewrite <- (mult_e a) in H1 at 2. rewrite <- H0 in H1. repeat rewrite mult_assoc in H1.\")")
    sendCommand(proc, "(Exec 110)")
    sendCommand(proc, "(Query ((sid 12) (pp ((pp_format PpStr)))) Goals)")
    parseAndPrintGoals(open("log.txt").readlines()[-1])
    sendCommand(proc, "(Add ()  \"assert ( (a <*> a) = e ). apply H.\")")
    sendCommand(proc, "(Add () \"assert ( (b <*> b) = e ). apply H.\")")
    sendCommand(proc, "(Exec 114)")
    sendCommand(proc, "(Query ((sid 16) (pp ((pp_format PpStr)))) Goals)")
    parseAndPrintGoals(open("log.txt").readlines()[-1])
    sendCommand(proc, "(Add () \"rewrite H2 in H1. rewrite <- mult_assoc in H1.\")")
    sendCommand(proc, "(Exec 18)")
    sendCommand(proc, "(Query ((sid 18) (pp ((pp_format PpStr)))) Goals)")
    parseAndPrintGoals(open("log.txt").readlines()[-1])
    sendCommand(proc, "(Add () \"rewrite H3 in H1.\")")
    sendCommand(proc, "(Exec 19)")
    sendCommand(proc, "(Query ((sid 19) (pp ((pp_format PpStr)))) Goals)")
    parseAndPrintGoals(open("log.txt").readlines()[-1])
    sendCommand(proc, "(Add () \"  rewrite (e_mult b) in H1. rewrite mult_e in H1.\")")
    sendCommand(proc, "(Exec 21)")
    sendCommand(proc, "(Query ((sid 21) (pp ((pp_format PpStr)))) Goals)")
    parseAndPrintGoals(open("log.txt").readlines()[-1])
    sendCommand(proc, "(Add () \"exact H1. Qed.\")")
    sendCommand(proc, "(Exec 23)")
    sendCommand(proc, "(Query ((sid 23) (pp ((pp_format PpStr)))) Goals)")
    parseAndPrintGoals(open("log.txt").readlines()[-1])
    proc.terminate()    

if __name__ == "__main__":
   main()