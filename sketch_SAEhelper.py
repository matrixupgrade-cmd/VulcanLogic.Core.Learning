import random
from itertools import product

# -------------------------------
# Same helper functions as before:
# random_substrate, possible_after, Reachable, basin, find_cycles, meta_step
# -------------------------------

# ... (reuse the code from previous cell) ...

# -------------------------------
# Batch simulation
# -------------------------------

def batch_simulation(num_runs=50, num_states=5, max_transitions=2, max_levels=10, seed=None):
    results = []
    for i in range(num_runs):
        s = None if seed is None else seed + i
        states, update = random_substrate(num_states, max_transitions, seed=s)
        hierarchy = build_hierarchy(update, levels=max_levels)
        # Record stats
        level_stats = []
        for level, (attractors, basins) in enumerate(hierarchy):
            level_stats.append({
                "level": level,
                "num_attractors": len(attractors),
                "basins": [basins[tuple(a)] for a in attractors]
            })
        # Self-nesting check
        self_nested_count = 0
        for i in range(1, len(hierarchy)):
            prev_attractors, prev_basins = hierarchy[i-1]
            curr_attractors, curr_basins = hierarchy[i]
            for A in curr_attractors:
                for B in prev_attractors:
                    if set(B) <= set(curr_basins[tuple(A)]):
                        self_nested_count += 1
        results.append({
            "run": i,
            "levels": len(hierarchy),
            "level_stats": level_stats,
            "self_nested_count": self_nested_count
        })
    return results

# -------------------------------
# Run batch and summarize
# -------------------------------
results = batch_simulation(num_runs=50, num_states=5, max_transitions=2, max_levels=10, seed=42)

# Summarize
total_levels = [r["levels"] for r in results]
total_self_nested = [r["self_nested_count"] for r in results]
total_attractors_final_level = [r["level_stats"][-1]["num_attractors"] for r in results]

print(f"Average levels until stabilization: {sum(total_levels)/len(total_levels):.2f}")
print(f"Average self-nesting occurrences: {sum(total_self_nested)/len(total_self_nested):.2f}")
print(f"Average attractors at final level: {sum(total_attractors_final_level)/len(total_attractors_final_level):.2f}")

# Optionally: histogram of final attractor counts
import matplotlib.pyplot as plt

plt.hist(total_attractors_final_level, bins=range(0, max(total_attractors_final_level)+2), color='skyblue', edgecolor='black')
plt.xlabel("Number of attractors at final level")
plt.ylabel("Frequency")
plt.title("Distribution of attractor counts at stabilization")
plt.show()
