import random
import math

# ==============================
# Parameters
# ==============================

NUM_NEURONS = 20
STEPS = 400

ARM_COUNT = 6
ARM_LENGTH = 0.08

NOISE = 0.01

POKE_INTERVAL = 25
POKE_FORCE = 0.05

# ==============================
# Neuron
# ==============================

class Neuron:
    def __init__(self):
        self.x = random.random()
        self.y = random.random()
        self.state = random.randint(1, 3)
        self.memory = self.state
        self.arms = [random.uniform(0, 2*math.pi) for _ in range(ARM_COUNT)]
        self.coupling = 0
        self.plasma_lock = 0  # >0 disables coupling

    def move(self):
        self.x = (self.x + NOISE * (random.random() - 0.5)) % 1.0
        self.y = (self.y + NOISE * (random.random() - 0.5)) % 1.0


neurons = [Neuron() for _ in range(NUM_NEURONS)]

# ==============================
# Arm Coupling (fast sub-layer)
# ==============================

def arm_update(neurons):
    for n in neurons:
        n.coupling = 0

    for n in neurons:
        if n.plasma_lock > 0:
            continue

        for angle in n.arms:
            ax = n.x + ARM_LENGTH * math.cos(angle)
            ay = n.y + ARM_LENGTH * math.sin(angle)

            for m in neurons:
                if m is n or m.plasma_lock > 0:
                    continue

                if math.hypot(ax - m.x, ay - m.y) < ARM_LENGTH * 0.6:
                    if n.state == m.state:
                        n.coupling += 1
                        m.coupling += 1
                    else:
                        n.coupling -= 1
                        m.coupling -= 1

        # arm jitter
        n.arms = [a + random.uniform(-0.4, 0.4) for a in n.arms]

# ==============================
# Neuron Update (slow layer)
# ==============================

def neuron_update(neurons):
    for n in neurons:

        if n.coupling < -1:
            n.state = random.randint(1, 3)
            n.plasma_lock = 3
            n.coupling = 0

        elif n.coupling > 1:
            n.state = n.memory

        else:
            n.state += random.choice([-1, 0, 1])
            n.state = max(1, min(3, n.state))

        n.memory = n.state

    for n in neurons:
        if n.plasma_lock > 0:
            n.plasma_lock -= 1

# ==============================
# Simulation
# ==============================

for step in range(STEPS):

    # Slow external poke
    if step % POKE_INTERVAL == 0:
        n = random.choice(neurons)
        n.x += random.uniform(-POKE_FORCE, POKE_FORCE)
        n.y += random.uniform(-POKE_FORCE, POKE_FORCE)

    # Fast sub-layer
    arm_update(neurons)

    # Slow layer
    neuron_update(neurons)

    for n in neurons:
        n.move()

print("Done.")
