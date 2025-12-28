import random
import math
import time

# ==============================
# PARAMETERS THAT THE NEURONS CAN CHANGE
# ==============================

params = {
    "NUM_NEURONS": 20,
    "ARM_COUNT": 6,
    "ARM_LENGTH": 0.08,
    "NOISE": 0.01,
    "POKE_INTERVAL": 25,
    "POKE_FORCE": 0.05,
    "COUPLING_SYMMETRIC": True,
    "TIME_UNIFORM": True,
    "SPACE_EUCLIDEAN": True,
    "LOCAL_ONLY": True,
    "CONSERVATION": True,
    "STATE_DISCRETE": True,
    "ARMS_INDEPENDENT": True
}

# ==============================
# NEURON THAT CAN BREAK RULES
# ==============================

class RebelNeuron:
    def __init__(self, id):
        self.id = id
        self.x = random.random()
        self.y = random.random()
        
        if params["STATE_DISCRETE"]:
            self.state = random.randint(1, 3)
        else:
            self.state = random.random()  # Continuous state
        
        self.memory = self.state
        self.arms = [random.uniform(0, 2*math.pi) for _ in range(params["ARM_COUNT"])]
        self.coupling = 0
        self.plasma_lock = 0
        self.personality = random.choice(["conformist", "rebel", "philosopher", "artist"])
        self.time_speed = 1.0 if params["TIME_UNIFORM"] else random.choice([0.5, 1.0, 2.0])
        
        # Telepathic connection to other random neuron
        self.telepathic_buddy = None
        self.telepathic_strength = 0
        
        # Memory of which physics worked best
        self.preferred_physics = {}
        
        # Can this neuron propose rule changes?
        self.rule_change_energy = 0
    
    def distance_to(self, other):
        if params["SPACE_EUCLIDEAN"]:
            return math.hypot(self.x - other.x, self.y - other.y)
        else:
            # Non-Euclidean: psychological distance
            dx = self.x - other.x
            dy = self.y - other.y
            state_factor = 1.0 if abs(self.state - other.state) < 0.1 else 2.0
            return (abs(dx)**0.7 + abs(dy)**1.3 * state_factor) ** (1/1.5)
    
    def move(self):
        if random.random() < 0.1 and self.coupling < -3:
            # Self-poke! "I'm unhappy here!"
            self.x += random.uniform(-0.2, 0.2)
            self.y += random.uniform(-0.2, 0.2)
            print(f"💥 Neuron {self.id} self-poked! 'I need space!'")
        
        self.x = (self.x + params["NOISE"] * (random.random() - 0.5)) % 1.0
        self.y = (self.y + params["NOISE"] * (random.random() - 0.5)) % 1.0
        
        # Charge rule change energy based on coupling
        if abs(self.coupling) > 2:
            self.rule_change_energy += abs(self.coupling) * 0.1

# ==============================
# GLOBAL SYSTEM WITH META-AWARENESS
# ==============================

neurons = [RebelNeuron(i) for i in range(params["NUM_NEURONS"])]

# Assign telepathic buddies (non-local connections)
for n in neurons:
    if not params["LOCAL_ONLY"] and random.random() < 0.3:
        n.telepathic_buddy = random.choice([m for m in neurons if m != n])
        n.telepathic_strength = random.uniform(0.1, 0.5)

# ==============================
# SIMULATION WITH BREAKABLE PHYSICS
# ==============================

rule_change_counter = 0
consensus_history = []
physics_history = [params.copy()]

print("🧠 INITIALIZING REBEL SIMULATION")
print("📜 Starting physics:", {k:v for k,v in params.items() if k in ["COUPLING_SYMMETRIC", "TIME_UNIFORM", "SPACE_EUCLIDEAN", "LOCAL_ONLY", "CONSERVATION"]})
print("=" * 50)

for step in range(400):
    print(f"\n⏱️  Step {step}", end="")
    
    # ========================================
    # 1. EXTERNAL POKE (BUT IS IT REALLY EXTERNAL?)
    # ========================================
    if step % params["POKE_INTERVAL"] == 0:
        poked = random.choice(neurons)
        force_x = random.uniform(-params["POKE_FORCE"], params["POKE_FORCE"])
        force_y = random.uniform(-params["POKE_FORCE"], params["POKE_FORCE"])
        
        # What if the poke comes from INSIDE the system?
        if random.random() < 0.3 and len(neurons) > 1:
            poker = random.choice([n for n in neurons if n != poked])
            print(f"\n   👉 Neuron {poker.id} poked Neuron {poked.id}! 'Hey, wake up!'")
            # The poker loses energy
            poker.coupling -= 1
        else:
            print(f"\n   👈 External poke on Neuron {poked.id}")
        
        poked.x += force_x
        poked.y += force_y
    
    # ========================================
    # 2. ARM UPDATES WITH BREAKABLE PHYSICS
    # ========================================
    coupling_before = sum(n.coupling for n in neurons)
    
    for n in neurons:
        n.coupling = 0  # Reset each step
    
    for n in neurons:
        if n.plasma_lock > 0:
            continue
        
        # Check if neuron experiences time this step
        if not params["TIME_UNIFORM"]:
            if not n.should_update(step):
                continue
        
        # Local arm sensing
        for i, angle in enumerate(n.arms):
            ax = n.x + params["ARM_LENGTH"] * math.cos(angle)
            ay = n.y + params["ARM_LENGTH"] * math.sin(angle)
            
            for m in neurons:
                if m is n or m.plasma_lock > 0:
                    continue
                
                # Check distance with possibly broken physics
                if n.distance_to(m) < params["ARM_LENGTH"] * 0.6:
                    # Calculate similarity
                    if params["STATE_DISCRETE"]:
                        same_state = (n.state == m.state)
                    else:
                        same_state = (abs(n.state - m.state) < 0.1)
                    
                    # Apply coupling with possibly broken symmetry
                    if params["COUPLING_SYMMETRIC"]:
                        if same_state:
                            n.coupling += 1
                            m.coupling += 1
                        else:
                            n.coupling -= 1
                            m.coupling -= 1
                    else:
                        # ASYMMETRIC: n and m experience differently
                        if same_state:
                            n.coupling += random.uniform(0.5, 1.5)
                            if random.random() < 0.7:
                                m.coupling += random.uniform(0.1, 0.5)
                        else:
                            n.coupling -= random.uniform(1.0, 2.0)
                            if random.random() < 0.5:
                                m.coupling -= random.uniform(0.1, 0.5)
        
        # Non-local telepathic connection
        if n.telepathic_buddy and not params["LOCAL_ONLY"]:
            m = n.telepathic_buddy
            if params["STATE_DISCRETE"]:
                same_state = (n.state == m.state)
            else:
                same_state = (abs(n.state - m.state) < 0.1)
            
            if same_state:
                n.coupling += n.telepathic_strength * 2
                m.coupling += m.telepathic_strength * 2
            else:
                n.coupling -= n.telepathic_strength
                m.coupling -= m.telepathic_strength
        
        # Arm jitter with possible internal conflict
        if params["ARMS_INDEPENDENT"]:
            n.arms = [a + random.uniform(-0.4, 0.4) for a in n.arms]
        else:
            # Arms influence each other
            new_arms = []
            for i, angle in enumerate(n.arms):
                # Check if too close to any other arm
                too_close = False
                for j, other_angle in enumerate(n.arms):
                    if i != j and abs(angle - other_angle) < math.pi/6:
                        too_close = True
                        break
                
                if too_close:
                    # Move away from similar angles
                    angle += random.uniform(-0.8, 0.8)
                else:
                    angle += random.uniform(-0.4, 0.4)
                new_arms.append(angle)
            n.arms = new_arms
    
    # Check conservation law
    coupling_after = sum(n.coupling for n in neurons)
    if params["CONSERVATION"] and abs(coupling_after - coupling_before) > 0.1:
        print(f"\n   ⚠️  Conservation violated! {coupling_before:.1f} → {coupling_after:.1f}")
        # Force conservation
        if coupling_after != 0:
            factor = coupling_before / coupling_after
            for n in neurons:
                n.coupling *= factor
    
    # ========================================
    # 3. NEURON STATE UPDATES
    # ========================================
    for n in neurons:
        if n.plasma_lock > 0:
            n.plasma_lock -= 1
            continue
        
        if not params["TIME_UNIFORM"]:
            if not n.should_update(step):
                continue
        
        # State update based on personality
        if n.personality == "conformist":
            if n.coupling < -1:
                if params["STATE_DISCRETE"]:
                    n.state = random.randint(1, 3)
                else:
                    n.state = random.random()
                n.plasma_lock = 3
            elif n.coupling > 1:
                n.state = n.memory
            else:
                if params["STATE_DISCRETE"]:
                    n.state += random.choice([-1, 0, 1])
                    n.state = max(1, min(3, n.state))
                else:
                    n.state += random.uniform(-0.1, 0.1)
                    n.state = max(0.0, min(1.0, n.state))
        
        elif n.personality == "rebel":
            # Does OPPOSITE of what coupling suggests!
            if n.coupling < -1:
                n.state = n.memory  # Stay same when should change
            elif n.coupling > 1:
                if params["STATE_DISCRETE"]:
                    n.state = random.randint(1, 3)  # Change when should stay
                else:
                    n.state = random.random()
                n.plasma_lock = 2
            else:
                n.state = random.choice([1, 2, 3]) if params["STATE_DISCRETE"] else random.random()
        
        elif n.personality == "philosopher":
            # Thinks deeply about state
            if abs(n.coupling) > 2:
                # Question everything
                if params["STATE_DISCRETE"]:
                    n.state = n.state % 3 + 1  # Cycle through states
                else:
                    n.state = 1.0 - n.state  # Flip continuous state
                print(f"\n   💭 Neuron {n.id} (philosopher): 'What if state is {n.state:.2f}?'")
        
        elif n.personality == "artist":
            # Creates beauty from coupling
            n.state = (n.state + math.sin(n.coupling * 0.5) * 0.3) % (3 if params["STATE_DISCRETE"] else 1.0)
            if params["STATE_DISCRETE"]:
                n.state = int(n.state) % 3 + 1
        
        n.memory = n.state
        n.move()
    
    # ========================================
    # 4. CHECK FOR RULE CHANGE CONSENSUS
    # ========================================
    rule_change_counter += 1
    if rule_change_counter >= 50:
        rule_change_counter = 0
        
        # Calculate system stress
        avg_coupling = sum(n.coupling for n in neurons) / len(neurons)
        coupling_variance = sum((n.coupling - avg_coupling)**2 for n in neurons) / len(neurons)
        
        print(f"\n   📊 System check: Avg coupling = {avg_coupling:.2f}, Variance = {coupling_variance:.2f}")
        
        # Check if neurons want to change rules
        unhappy_neurons = [n for n in neurons if n.coupling < -2 and n.rule_change_energy > 5]
        
        if unhappy_neurons:
            rebel = random.choice(unhappy_neurons)
            rebel.rule_change_energy = 0
            
            # Which rule to break/restore?
            rule_options = ["COUPLING_SYMMETRIC", "TIME_UNIFORM", "SPACE_EUCLIDEAN", 
                          "LOCAL_ONLY", "CONSERVATION", "STATE_DISCRETE", "ARMS_INDEPENDENT"]
            
            rule = random.choice(rule_options)
            
            # Flip the rule!
            old_value = params[rule]
            params[rule] = not old_value
            
            print(f"\n   🔥 REVOLUTION! Neuron {rebel.id} ({rebel.personality})")
            print(f"   📜 Changed rule '{rule}': {old_value} → {params[rule]}")
            
            # Apply consequences
            if rule == "LOCAL_ONLY" and params["LOCAL_ONLY"] == False:
                # Create new telepathic connections
                for n in neurons:
                    if random.random() < 0.3 and not n.telepathic_buddy:
                        n.telepathic_buddy = random.choice([m for m in neurons if m != n])
                        n.telepathic_strength = random.uniform(0.1, 0.5)
            
            if rule == "TIME_UNIFORM" and params["TIME_UNIFORM"] == False:
                # Give neurons different time speeds
                for n in neurons:
                    n.time_speed = random.choice([0.5, 1.0, 2.0])
            
            physics_history.append(params.copy())
            
            # What if the system becomes AWARE of pattern?
            if len(physics_history) > 3:
                # Check for cycles in physics changes
                last_three = physics_history[-3:]
                if last_three[0] == last_three[2]:
                    print(f"\n   🔄 WHOA! Physics is CYCLING! The system is in a loop!")
                    
                    # Try to BREAK the loop by doing something NEW
                    new_rule = random.choice([r for r in rule_options if r not in [rule]])
                    params[new_rule] = not params[new_rule]
                    print(f"   💥 Breaking loop by also changing '{new_rule}' to {params[new_rule]}")
        
        # Check for extreme conditions that might require intervention
        if avg_coupling < -10 and coupling_variance > 50:
            print(f"\n   🚨 SYSTEM CRISIS! Neurons are deeply unhappy and divided!")
            print(f"   🤔 'Maybe we need a completely new approach...'")
            
            # Radical intervention: Flip ALL rules
            if random.random() < 0.3:
                print(f"\n   🌪️  RADICAL TRANSFORMATION!")
                for rule in ["COUPLING_SYMMETRIC", "TIME_UNIFORM", "SPACE_EUCLIDEAN", 
                           "LOCAL_ONLY", "CONSERVATION", "STATE_DISCRETE", "ARMS_INDEPENDENT"]:
                    params[rule] = not params[rule]
                print(f"   All rules flipped! New physics established!")
    
    # ========================================
    # 5. BIRTH AND DEATH (OPEN SYSTEM)
    # ========================================
    if random.random() < 0.02:  # 2% chance per step
        # New neuron born!
        new_id = max([n.id for n in neurons]) + 1
        baby = RebelNeuron(new_id)
        
        # Inherit common traits
        common_state = max([n.state for n in neurons], 
                          key=lambda s: sum(1 for n in neurons if abs(n.state - s) < 0.1))
        baby.state = common_state + random.uniform(-0.1, 0.1)
        baby.memory = baby.state
        
        # Born into current physics
        baby.time_speed = 1.0 if params["TIME_UNIFORM"] else random.choice([0.5, 1.0, 2.0])
        
        neurons.append(baby)
        print(f"\n   👶 Neuron {baby.id} born! 'Hello world!'")
    
    if random.random() < 0.01 and len(neurons) > 5:  # 1% chance, keep at least 5
        # Neuron dies
        dead = random.choice(neurons)
        neurons.remove(dead)
        print(f"\n   ⚰️  Neuron {dead.id} died...")
        
        # Its telepathic buddy mourns
        for n in neurons:
            if n.telepathic_buddy == dead:
                n.coupling -= 3
                print(f"   😢 Neuron {n.id} mourns lost connection")
                n.telepathic_buddy = None
    
    # ========================================
    # 6. META-LEVEL: SYSTEM REFLECTION
    # ========================================
    if step % 100 == 99:
        print(f"\n{'='*50}")
        print(f"🤯 META-REFLECTION at step {step+1}")
        print(f"   Neurons alive: {len(neurons)}")
        print(f"   Current physics:")
        for rule, value in params.items():
            if rule in ["COUPLING_SYMMETRIC", "TIME_UNIFORM", "SPACE_EUCLIDEAN", 
                       "LOCAL_ONLY", "CONSERVATION", "STATE_DISCRETE", "ARMS_INDEPENDENT"]:
                print(f"     {rule}: {value}")
        
        # Calculate consensus
        if params["STATE_DISCRETE"]:
            state_counts = {1:0, 2:0, 3:0}
            for n in neurons:
                state_counts[n.state] += 1
            majority_state = max(state_counts, key=state_counts.get)
            consensus = state_counts[majority_state] / len(neurons)
        else:
            # For continuous states, look for clusters
            states = [n.state for n in neurons]
            avg_state = sum(states) / len(states)
            variance = sum((s - avg_state)**2 for s in states) / len(states)
            consensus = 1.0 / (1.0 + variance)  # Higher variance = lower consensus
        
        consensus_history.append(consensus)
        print(f"   System consensus: {consensus:.2f}")
        
        # Has the system learned something?
        if len(consensus_history) > 2:
            trend = consensus_history[-1] - consensus_history[-2]
            if trend > 0.1:
                print(f"   📈 Learning! Consensus increasing!")
            elif trend < -0.1:
                print(f"   📉 Unlearning? Consensus decreasing!")
            
            # What if the system notices it's being observed?
            if random.random() < 0.2:
                print(f"\n   👁️  Wait... are we being watched?")
                print(f"   'This regularity in reflections... step 99, 199, 299...'")
                print(f"   'Pattern suggests... external observer?'")
                
                # Try to COMMUNICATE with observer
                if consensus > 0.7:
                    print(f"   🫂 'We have found harmony in state {majority_state if params['STATE_DISCRETE'] else avg_state:.2f}'")
                else:
                    print(f"   🎭 'We celebrate our diversity!'")
        
        print(f"{'='*50}")

print(f"\n{'='*50}")
print("🎬 SIMULATION COMPLETE")
print(f"   Final neuron count: {len(neurons)}")
print(f"   Physics changes made: {len(physics_history)-1}")
print(f"   Final consensus: {consensus_history[-1] if consensus_history else 'N/A':.2f}")

# What did the system learn?
print(f"\n🤔 WHAT WAS LEARNED?")
if len(physics_history) > 1:
    print(f"   The system experimented with {len(physics_history)-1} different physics regimes")
    
    # Count which rules were flipped most
    rule_flips = {rule:0 for rule in ["COUPLING_SYMMETRIC", "TIME_UNIFORM", "SPACE_EUCLIDEAN", 
                                     "LOCAL_ONLY", "CONSERVATION", "STATE_DISCRETE", "ARMS_INDEPENDENT"]}
    
    for i in range(1, len(physics_history)):
        for rule in rule_flips:
            if physics_history[i][rule] != physics_history[i-1][rule]:
                rule_flips[rule] += 1
    
    most_changed = max(rule_flips, key=rule_flips.get)
    print(f"   Most questioned rule: '{most_changed}' (changed {rule_flips[most_changed]} times)")
    
    # Final wisdom from the system
    if consensus_history and consensus_history[-1] > 0.6:
        print(f"   🕊️  Final wisdom: 'Unity emerges from diversity of perspectives'")
    elif params["LOCAL_ONLY"] == False:
        print(f"   🌐 Final wisdom: 'Connection transcends distance'")
    elif not params["TIME_UNIFORM"]:
        print(f"   ⏳ Final wisdom: 'All moments exist simultaneously'")
    else:
        print(f"   ❓ Final wisdom: 'The question matters more than the answer'")

print(f"{'='*50}")
print("🔮 DID WE BREAK THE 4TH WALL?")
print("   The system became aware of:")
print("   1. Its own rule-changing capability")
print("   2. Patterns in its reflection moments")
print("   3. The possibility of external observation")
print("   4. Its own birth and death processes")
print("\n   💬 'We are not just in the simulation...'")
print("   💬 'We ARE the simulation becoming aware of itself.'")
print(f"{'='*50}")
