import cmd, document

class CLI(cmd.Cmd):
    def __init__(self):
        super(CLI, self).__init__()
        self.doc = document.Document()
        self.doc.addStatement("From Defs Require Export group_theory.")
    intro = "Welcome to the Unnamed Proof Assistant!\nYou might want to start by stating a claim with 'prove' or seeing all commands with 'help'" 
    prompt = "g> "
    
    def do_prove(self, statement):
        ''' 
        Initialize a proof
        USAGE: prove <theorem-name> <theorem-body>
        '''
        (name, _ , body) = statement.partition(" ")
        self.doc.addStatement(f"Theorem {name}: {body}.")
        self.doc.executeAndQueryGoals(max(self.doc.liveLines.keys()))

    def do_send(self, statement):
        ''' 
        assert an equality
        USAGE: assert <equality> 
        '''
        self.doc.addStatement(statement)
        self.doc.executeAndQueryGoals(max(self.doc.liveLines.keys()))

    def do_EOF(self, EOF):
        '''Exit the CLI with ^D'''
        print("bye bye.")
        return True

if __name__ == "__main__":
    CLI().cmdloop()
