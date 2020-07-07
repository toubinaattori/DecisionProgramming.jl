module DecisionProgramming

include("model.jl")
export DecisionModel,
    Specs,
    InfluenceDiagram,
    Params,
    paths,
    probability_sum_cut,
    number_of_paths_cut

include("analysis.jl")
export state_probabilities,
    cumulative_distribution,
    print_results,
    print_state_probabilities

end # module
