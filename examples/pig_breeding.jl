using Printf
using JuMP, Gurobi
using DecisionProgramming

# Parameters
N = 4 # Number of months
health = [3*k - 2 for k in 1:N] # health of the pig
test = [3*k - 1 for k in 1:(N-1)] # whether to test the pig
treat = [3*k for k in 1:(N-1)] # whether to treat the pig
cost = [(3*N - 2) + k for k in 1:(N-1)] # treatment cost
price = [(3*N - 2) + N] # sell price

# Influence diagram parameters
C = health ∪ test
D = treat
V = cost ∪ price
A = Vector{Pair{Int, Int}}()
S_j = Vector{Int}()

# Construct arcs
add_arcs(from, to) = append!(A, (i => j for (i, j) in zip(from, to)))
add_arcs(health[1:end-1], health[2:end])
add_arcs(health[1:end-1], test)
add_arcs(treat, health[2:end])
add_arcs(treat, cost)
add_arcs(health[end], price)
append!(A, (test[k] => treat[k2] for k in 1:(N-1) for k2 in k:(N-1)))
append!(A, (treat[k] => treat[k2] for k in 1:((N-1)-1) for k2 in (k+1):(N-1)))

# Construct states
S_j = zeros(Int, length(C)+length(D))
S_j[health] = fill(2, length(health))
S_j[test] = fill(2, length(test))
S_j[treat] = fill(2, length(treat))

# Probabilities
X = Dict{Int, Array{Float64}}()

# h_1
begin
    i = health[1]
    p = zeros(S_j[i])
    p[1] = 0.1
    p[2] = 1.0 - 0.1
    X[i] = p
end

# h_i, i≥2
for (i, j, k) in zip(health[1:end-1], treat, health[2:end])
    p = zeros(S_j[i], S_j[j], S_j[k])
    p[2, 2, 1] = 0.2
    p[2, 2, 2] = 1.0 - 0.2
    p[2, 1, 1] = 0.1
    p[2, 1, 2] = 1.0 - 0.1
    p[1, 2, 1] = 0.9
    p[1, 2, 2] = 1.0 - 0.9
    p[1, 1, 1] = 0.5
    p[1, 1, 2] = 1.0 - 0.5
    X[k] = p
end

# t_i
for (i, j) in zip(health, test)
    p = zeros(S_j[i], S_j[j])
    p[1, 1] = 0.8
    p[1, 2] = 1.0 - 0.8
    p[2, 2] = 0.9
    p[2, 1] = 1.0 - 0.9
    X[j] = p
end

# Consequences
# 1 => treatment consequence
# 2 => no-treament consequence
# 3 => ill at N-month consequence
# 4 => healthy at N-month consequence
Y = Dict{Int, Array{Float64}}()
for i in cost
    Y[i] = [-100, 0]
end
for i in price
    Y[i] = [300, 1000]
end

# Model
diagram = InfluenceDiagram(C, D, V, A, S_j)
specs = Specs()
params = Params(diagram, X, Y)
model = DecisionModel(specs, diagram, params)


println("--- Optimization ---")
optimizer = optimizer_with_attributes(
    Gurobi.Optimizer,
    "IntFeasTol"      => 1e-9,
    "LazyConstraints" =>    1,
    "TimeLimit"       => 2*60,
    "Heuristics"      =>  .00,  # 0% time spend on heuristics (lazy cuts need to be re-added if heuristic is used in root node)
    "BranchDir"       =>    1,  # -1 ... 1: 1 = branch up
    "VarBranch"       =>    0,  # -1 ... 3: 0 = pseudo costs, 3 = Strong branching
    "Cuts"            =>    0,  # -1 ... 3: 0 = all cuts off (use lazy cuts instead that exploit problem structure)
    "DisplayInterval"   => 5
)
set_optimizer(model, optimizer)
optimize!(model)

# -- Results ---
I_j = diagram.I_j
S_j = diagram.S_j
πsol = model[:π]
z = model[:z]

utility(s) = sum(Y[v][s[I_j[v]]...] for v in V)

println()
println("--- Active Paths ---")
println("path | probability | utility | expected utility")
for s in paths(S_j)
    πval = value(πsol[s...])
    isapprox(πval, 0, atol=1e-3) && continue
    u = utility(s)
    eu = πval * u
    @printf("%s | %0.3f | %0.3f | %0.3f \n", s, πval, u, eu)
end

expected_utility = sum(value(πsol[s...]) * utility(s) for s in paths(S_j))
println("Expected utility: ", expected_utility)

# for i in D
#     println("Decisions at node $i.")
#     # TODO: which subpaths are equal to 1
#     zval = value.(z[i])
# end
