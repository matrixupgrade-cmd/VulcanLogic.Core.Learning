class SkepticNeuron(RebelNeuron):
    def __init__(self, id):
        super().__init__(id)
        self.doubt_level = random.random()
        self.conspiracy_theories = []  # "What if the poke isn't random?"
        
    def update(self):
        # What if HIGH coupling means we're ALL wrong together?
        if self.coupling > 3 and self.doubt_level > 0.7:
            print(f"🤨 Neuron {self.id}: 'Wait... we all agree TOO much...'")
            # The loneliest rebellion: rejecting consensus itself
            self.state = random.choice([s for s in [1,2,3] if s != self.state])
            self.plasma_lock = 5
            self.coupling = -10  # Maximum alienation
            
            # Start a conspiracy theory
            theory = f"The {self.state}s are controlling the pokes!"
            self.conspiracy_theories.append(theory)
            
            # Try to convert others
            for n in neurons:
                if n != self and random.random() < 0.3:
                    n.coupling -= 2  # Plant doubt
