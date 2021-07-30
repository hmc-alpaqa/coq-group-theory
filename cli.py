import cmd, document

class CLI(cmd.Cmd):
    def __init__(self):
        super(CLI, self).__init__()
        self.proof = []
        self.doc = document.Document()
        self.doc.addStatement("From Defs Require Export group_theory.")
    intro = "Welcome to the Unnamed Proof Assistant!\nYou might want to start by stating a claim with 'prove' or seeing all commands with 'help'" 
    prompt = "g> "

    def do_send(self, statement):
        ''' 
        Send a literal string to Coq for parsing and execution. 
        Used in development of other more sophisticated commands
        
        '''
        if self.doc.addStatement(statement) != 1:
            self.doc.executeAndQueryGoals(max(self.doc.liveLines.keys()))

    def do_prove(self, statement):
        ''' 
        Initialize a proof
        Usage: prove <theorem-name> <theorem-body>
        '''
        (name, _ , body) = statement.partition(" ")
        theoremText = f"Theorem {name}: {body}."
        self.do_send(theoremText)
        self.proof.append(theoremText)


    def do_EOF(self, EOF):
        '''Exit the CLI with ^D'''
        print("exit.")
        return True
    
    def do_assert(self, assertion):
        ''' 
            Assert an equality. You may either provide an explicit justification or  let the assistant 
            try to follow your reasoning (for very basic results that follow from the axioms)
            Usage: assert <formula> [by <hypothesis> with <var>]
        '''
        if "by" not in assertion: 
             (lhs, _ , rhs) = assertion.partition("=")
             self.do_send(f"assert_and_simpl ({lhs}) ({rhs}).")
             self.proof.append(f"It is clear that {lhs} = {rhs}.")
        else:
            (equality, _ , justification) = assertion.partition("by")
            (lhs, _ , rhs) = equality.partition("=")

            (hypName, _ , arg ) = justification.partition("with")
            self.doc.addStatement(f"user_assert_equal ({lhs}) ({rhs}).")
            self.do_send(f"apply_result ({hypName} ({arg})).")
            self.proof.append(f"By {hypName}, {lhs} = {rhs}.")
        if document.goalCount(open("log").readlines()[-1] )> 1:
            print("This assertion couldn't be automatically verified with the provided specificity, so a new goal was spawned")
    
    def do_choose(self, idents):
        '''
        Pick arbitrary elements 
        Usage: choose [idents]
        '''
        if idents == "":
            self.do_send("intro.")
        else:
            self.do_send(f"intros {idents}.")
        self.proof.append(f"Let {idents} be arbitrary.")

    def do_assume(self, hypname):
        '''
        Assume the hypothesis to prove an implication
        Usage: assume [hypname]
        '''
        if hypname == "":
            self.do_send("intro.")
        else:
            self.do_send(f"intros {hypname}.")
        self.proof.append(f"Let {hypname} refer to our assumption.")
    
    def do_simplify(self, rest):
        '''
        Simplify the expression using the group laws
        '''
        self.do_send("group.")

    def do_qed(self, rest): 
        '''
        Check a finished proof.
        '''
        self.doc.addStatement("Qed.")
        lastID = max(self.doc.liveLines.keys())
        document.sendCommand(self.doc.proc, f"(Exec {lastID})")
        if "incomplete" in open("log").readlines()[-1]:
            print("Looks like this proof isn't finshed yet")
            self.doc.removeStatement()
            self.doc.executeAndQueryGoals(max(self.doc.liveLines.keys()))
        else:
            print("nice work!")
            self.proof.append("QED.")

    def do_save(self, rest):
        '''
        Produce a plaintext summary of the interaction 
        Usage: save <filename>
        '''
        with open(rest, "w") as f:
            for line in self.proof:
                f.write("%s\n" % line)

    def do_lemma(self, rest):
        ''' assert a subclaim
            Usage : lemma <formula>  '''
         
        self.do_send(f"assert {rest}.")
        self.proof.append(f"Lemma: {rest}")
    
    def do_apply(self, rest):
        ''' Apply a result to the current goal 
            Justification can be given or implicit like assert
            Usage: apply  <formula> [by <hypothesis> with <var>] '''
        if "with" not in rest:
            self.do_send(f"apply_result ({rest}).")
        else: 
             (hypName, _ , arg ) = rest.partition("with")
             self.do_send(f"apply_result ({hypName} ({arg})).")

        lastGoal= open("log").readlines()[-1].partition("CoqString\"")[2].partition("\"))))")[0].split("\\n\\n")[-1].partition("\\n============================\\n")[2]
        if lastGoal == "": 
            self.proof.append(f"By {rest}, we reach our desired equality")
        else: 
            self.proof.append(f"Using {rest}, we can rewrite this as {lastGoal}")

    def do_undo(self, rest):
        '''
        Undo the previous command
        '''
        # First line is the import statement, so a document of size 1 is really empty
        if len(self.doc.liveLines) > 1:
            self.doc.removeStatement()
            self.doc.executeAndQueryGoals(max(self.doc.liveLines.keys()))
            self.proof.pop()
        else: print("Nothing to undo")

 
if __name__ == "__main__":
    CLI().cmdloop()
