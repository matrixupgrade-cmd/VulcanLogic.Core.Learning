import pandas as pd
import plotly.graph_objects as go
import numpy as np

# Load CSV exported from Lean
csv_file = "hierarchy_norms.csv"

levels = []
current_level = None
data = []

with open(csv_file, "r") as f:
    for line in f:
        line = line.strip()
        if line.startswith("Level"):
            current_level = int(line.split()[1])
        elif line:
            name, l2, l_inf, sum0, self_amp, pert = line.split(",")
            data.append({
                "level": current_level,
                "name": name,
                "L2": float(l2),
                "L∞": float(l_inf),
                "sum_L2": float(sum0),
                "self_amp": self_amp == "True",
                "pert": float(pert)
            })

df = pd.DataFrame(data)

# Build edges and compute contribution weight
edges = []
for idx, row in df.iterrows():
    parent_candidates = df[(df["level"] == row["level"] - 1)]
    for _, parent in parent_candidates.iterrows():
        if abs(parent["L2"]) <= row["sum_L2"] + 1e-6: 
            weight = row["L2"] / (parent["L2"] + 1e-6)
            edges.append({"parent": parent["name"], "child": row["name"], "weight": weight})

# Map names to coordinates
name_to_coords = {}
for _, row in df.iterrows():
    name_to_coords[row["name"]] = (row["L2"], row["L∞"], row["level"])

# Scatter nodes
x, y, z, base_size, color, text = [], [], [], [], [], []
for _, row in df.iterrows():
    x.append(row["L2"])
    y.append(row["L∞"])
    z.append(row["level"])
    base_size.append(row["pert"]*20)
    color.append(row["self_amp"])
    text.append(f"{row['name']}<br>L2={row['L2']:.2f}<br>L∞={row['L∞']:.2f}<br>pert={row['pert']:.3f}")

scatter = go.Scatter3d(
    x=x, y=y, z=z, mode='markers+text', text=text, textposition="top center",
    marker=dict(size=[s*0.05 for s in base_size], color=color, colorscale='Viridis', opacity=0.8)
)

# Edge traces
edge_traces = []
for e in edges:
    px, py, pz = name_to_coords[e["parent"]]
    cx, cy, cz = name_to_coords[e["child"]]
    edge_traces.append(
        go.Scatter3d(
            x=[px, cx], y=[py, cy], z=[pz, cz],
            mode='lines', line=dict(color='gray', width=2*e["weight"]), hoverinfo='none'
        )
    )

# Animation frames: perturbation growth + highlight strongest L2 path
frames = []
time_steps = 20
# Identify max-L2 path: greedily pick child with max L2 at each level
max_path = []
level = 0
current_nodes = df[df["level"]==level]
if not current_nodes.empty:
    node = current_nodes.loc[current_nodes["L2"].idxmax()]["name"]
    max_path.append(node)
    while True:
        level += 1
        next_nodes = [e["child"] for e in edges if e["parent"]==node]
        if not next_nodes:
            break
        node = df[df["name"].isin(next_nodes)].loc[df["L2"].idxmax()]["name"]
        max_path.append(node)

for t in range(time_steps):
    scale = (t+1)/time_steps
    sizes = [s*scale for s in base_size]
    # Highlight edges along max-L2 path
    frame_edge_traces = []
    for e in edges:
        px, py, pz = name_to_coords[e["parent"]]
        cx, cy, cz = name_to_coords[e["child"]]
        if e["parent"] in max_path and e["child"] in max_path:
            color_edge = 'red'
            width_edge = 6
        else:
            color_edge = 'gray'
            width_edge = 2*e["weight"]
        frame_edge_traces.append(
            go.Scatter3d(
                x=[px, cx], y=[py, cy], z=[pz, cz],
                mode='lines', line=dict(color=color_edge, width=width_edge), hoverinfo='none'
            )
        )
    frame = go.Frame(
        data=[go.Scatter3d(
            x=x, y=y, z=z, mode='markers+text', text=text, textposition="top center",
            marker=dict(size=sizes, color=color, colorscale='Viridis', opacity=0.8)
        )] + frame_edge_traces,
        name=f'frame{t}'
    )
    frames.append(frame)

# Build figure
fig = go.Figure(
    data=[scatter] + edge_traces,
    frames=frames
)

fig.update_layout(
    scene=dict(
        xaxis_title='L2 Norm',
        yaxis_title='L∞ Norm',
        zaxis_title='Hierarchy Level'
    ),
    title="Animated Hierarchy: Max-L2 Path Highlight & Perturbation Propagation",
    updatemenus=[dict(type="buttons",
                      buttons=[dict(label="Play", method="animate",
                                    args=[None, {"frame": {"duration": 200, "redraw": True}, "fromcurrent": True}]),
                               dict(label="Pause", method="animate",
                                    args=[[None], {"frame": {"duration": 0, "redraw": False}, "mode": "immediate"}])])]
)

# Export HTML
fig.write_html("Depository/hierarchy_norms_animated_maxL2.html", include_plotlyjs='cdn')
print("✅ Animated HTML saved to Depository/hierarchy_norms_animated_maxL2.html")
