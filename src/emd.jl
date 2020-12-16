using DataStructures
using OptimalTransport
using BenchmarkTools
using Profile
using FlameGraphs
using Plots
using TimerOutputs

# This function produces a basic feasible starting point in place into P and
# inputs the sparsity (tree) structure into left & right. left[i] & right[j] are BitSets,
# essentially implementing a set with fast inclusion, addition and deletion operations.
function NorthWest!(left, right, P, a, b)
    n = length(a)
    m = length(b)
    rowsum = zeros(n)
    colsum = zeros(m)
    for j in 1:m
        for i in 1:n
            if isapprox(colsum[j], b[j])
                break
            end
            P[i,j] = min(b[j]-colsum[j], a[i]-rowsum[i])
            rowsum[i] += P[i,j]
            colsum[j] += P[i,j]
            if P[i,j] > 0
                push!(left[i], UInt32(j))
                push!(right[j], UInt32(i))
            end
        end
    end
end

# Given the tree defined by left & right, calculates the dual potentials u,v, in place
# using DFS. Pretty sure that this function actually works as intended.
function update_potential!(u, v, C, left, right, state, max_iter = 10000)
    n = length(u)
    m = length(v)
    # Since tree structure might in fact be a forest, need to start DFS from
    # an arbitrary root in each disjoint tree. We keep track of the updated
    # nodes on the left of the bipartite graph in 'unchanged'.
    sgn = state[1]
    for i in 1:n
        if !(state[i] == sgn)
            continue
        end
        u[i] = 0
        DFS_potential!(i, 0, u, v, C, left, right, state, sgn)
    end
end


# Helper for update_potential(). side = {0,1} = {left,right}. Basically a standard DFS implementation
function DFS_potential!(node, side, u, v, C, left, right, state, sgn)
    if side == 0
        # If have already visited this node, then return
        if state[node] != sgn
            return
        end
        state[node] = !state[node]
        for neighbour in left[node]
            v[neighbour] = C[node,neighbour] - u[node]
            DFS_potential!(neighbour, 1, u, v, C, left, right, state, sgn)
        end
    else
        for neighbour in right[node]
            u[neighbour] = C[neighbour, node] - v[node]
            DFS_potential!(neighbour, 0, u, v, C, left, right, state, sgn)
        end
    end
end


# Finds the entering edge by finding the minimal difference C - u - v over
# all edges. 1 ≦ blk_size ≦ mn is the size of the block used in block search,
# while 1 ≦ blk_start ≦ mn is the starting edge of the block search. (bad_i[k], bad_j[k])ₖ
# is a list of edges to avoid because they have been tried and don't improve the objective.
function find_entering(u, v, C, blk_size, blk_start, res, bad_i, bad_j, bad_index)
    n = length(u)
    m = length(v)
    currmin = 0
    enter_i = enter_j = -1

    # (i-1)*m + j = blk_start ∈ [1 ... mn]
    start_j = blk_start % m
    start_i = (blk_start - start_j)/m + 1

    counter = 1
    for i in 1:n
        for j in 1:m
            ii = Int((i + start_i - 1)%n + 1)
            jj = Int((j + start_j - 1)%m + 1)
            if C[ii,jj] - u[ii] - v[jj] < currmin && (bad_index == 0 || valid(bad_i, bad_j, bad_index, ii,jj))
                enter_i = ii
                enter_j = jj
                currmin = C[ii,jj] - u[ii] - v[jj]
            end
            counter += 1
            if (counter-1)%blk_size == 0
                if enter_i > 0
                    res[1] = enter_i
                    res[2] = enter_j
                    res[3] = 0
                    return
                end
            end
        end
    end
    if enter_i < 0
        res[1] = -1
        res[2] = -1
        res[3] = 1
        return
    end
    res[1] = enter_i
    res[2] = enter_j
    res[3] = 0
end

# Given arrays bad_i, bad_j and (i,j) returns true if (i,j) == (bad_i[k], bad_j[k])
# for some k, and false otherwise.
function valid(bad_i, bad_j, bad_index, i, j)
    for k in 1:bad_index
        if (bad_i[k], bad_j[k]) == (i,j)
            return false
        end
    end
    return true
end

# Given an edge (tail, head) we find the unique cycle containing it using BFS.
# We start a BFS search starting with the edge (tail, head) and save the results
# in left_parents & right_parents. left_parents[i] is the parent of the left node i
# and right_parents[j] is the parent of the right node j.
function find_cycle(tail, head, left, right, left_parents, right_parents, node_queue, side_queue, max_iter = 10000)
    l = length(node_queue)
    n_left = n_right = 1
    s_left = s_right = 1
    leftcounter = rightcounter = 1
    node_queue[1] = head
    side_queue[1] = true
    # side = {false,true} is {left,right} hand side respectively
    while leftcounter <= rightcounter && max_iter > 0
        max_iter -= 1
        node = node_queue[n_left]
        side = side_queue[s_left]
        n_left = (n_left + 1)%l + 1
        s_left = (s_left + 1)%l + 1
        leftcounter += 1
        if side
            for neighbour in right[node]
                # Need the next condition to avoid turning around straight away
                if right_parents[node] != neighbour
                    # Check whether the loop has closed
                    if neighbour == tail
                        left_parents[tail] = node
                        # Return true if have found a cycle
                        return true
                    end
                    left_parents[neighbour] = node
                    n_right = (n_right + 1)%l + 1
                    s_right = (s_right + 1)%l + 1
                    rightcounter += 1
                    node_queue[n_right] = neighbour
                    side_queue[s_right] = false
                end
            end
        else
            for neighbour in left[node]
                if left_parents[node] != neighbour
                    right_parents[neighbour] = node
                    n_right = (n_right + 1)%l + 1
                    s_right = (s_right + 1)%l + 1
                    rightcounter += 1
                    node_queue[n_right] = neighbour
                    side_queue[s_right] = true
                end
            end
        end
    end
    # return false because no cycle found
    return false
end


# Calculates the minimum value of P[i,j] along the reverse edges of the detected cycle.
function calculate_improvement(i, j, left_parents, right_parents, P, res, max_iter = 10000)
    curr_i = i
    curr_j = left_parents[i]
    imp = P[i,curr_j]
    imp_i = curr_i
    imp_j = curr_j
    curr_i = right_parents[curr_j]

    while curr_i != i && max_iter > 0
        max_iter -= 1
        curr_j = left_parents[curr_i]
        if P[curr_i, curr_j] < imp
            imp_i = curr_i
            imp_j = curr_j
            imp = P[curr_i, curr_j]
        end
        curr_i = right_parents[curr_j]
    end
    res[1] = imp_i
    res[2] = imp_j
    return imp
end

# Given starting arc (i,j) improvement imp, and leaving edge (imp_i, imp_j), updates
# the tree structure in that it: 1) updates P using 'imp' 2) removes leaving edge.
function update_tree(i, j, imp, imp_i, imp_j, P, left, right, left_parents, right_parents, max_iter = 10000)
    curr_i = i
    curr_j = j
    P[curr_i, curr_j] += imp
    curr_j = left_parents[curr_i]
    P[curr_i, curr_j] -= imp
    curr_i = right_parents[curr_j]
    while curr_i != i && max_iter > 0
        max_iter -= 1
        P[curr_i, curr_j] += imp
        curr_j = left_parents[curr_i]
        P[curr_i, curr_j] -= imp
        curr_i = right_parents[curr_j]
    end
    delete!(left[imp_i], imp_j)
    delete!(right[imp_j], imp_i)
end

# Calculates inner product between two commensurate matrices.
function objective(P, C)
    return vec(P)'*vec(C)
end


# Returns optimal coupling between measures a,b wrt cost matrix C using Network Simplex.
# Block search is used with block size = α ⋅ m ⋅ n .
function my_emd(a, b, C; α = .05, max_iter = 10000)
    n = length(a)
    m = length(b)

    # left[i] is the set of nodes on the right that node i on the left is connected to.
    # right[j] is the set of nodes on the left that node j on the right is connecte to.
    left = Array{BitSet}(undef, n)
    right = Array{BitSet}(undef, m)

    # Initializing the arrays of sets
    for i in 1:n
        left[i] = BitSet()
    end
    for j in 1:m
        right[j] = BitSet()
    end

    # Allocating memory for coupling matrix
    P = zeros(n,m)

    # Initializing potentials
    u = zeros(n)
    v = zeros(m)

    # Initializing coupling matrix
    NorthWest!(left, right, P, a, b)

    # Allocating memory for cycle search
    left_parents = Vector{UInt32}(undef, n)
    right_parents = Vector{UInt32}(undef, m)
    enter_i = -1
    enter_j = -1
    node_queue = Vector{UInt32}(undef, n+m)
    side_queue = Vector{Bool}(undef, n+m)

    # Variables for block search
    blk_size = max(10, floor(α*m*n))
    blk_start = 1

    # Initializing variable to be used in update_potential()
    unchanged = Vector{Bool}(undef, n)
    fill!(unchanged, true)

    # Cache memory
    res = [0,0,0]
    res_float = [.0, .0]

    # Keep track of edges that have already been tried and don't improve objective
    bad_i = Vector{UInt32}(undef, 20)
    bad_j = Vector{UInt32}(undef, 20)
    bad_index = 0

    while true && max_iter > 0
        max_iter -= 1
        update_potential!(u, v, C, left, right, unchanged)

        prev_i = enter_i
        prev_j = enter_j
        find_entering(u, v, C, blk_size, blk_start, res, bad_i, bad_j, bad_index)
        enter_i = res[1]
        enter_j = res[2]
        done = res[3]
        blk_start += blk_size
        blk_start = (blk_start - 1)%(m*n) + 1

        if done > 0
            return P
        end

        # Add entering edge to tree (creating a unique cycle)
        push!(left[enter_i], enter_j)
        push!(right[enter_j], enter_i)
        edges = 0

        right_parents[enter_j] = enter_i
        is_cycle = find_cycle(enter_i, enter_j, left, right, left_parents, right_parents, node_queue, side_queue)

        if is_cycle
            bad_index = 0
            imp = calculate_improvement(enter_i, enter_j, left_parents, right_parents, P, res)
            imp_i = res[1]
            imp_j = res[2]
            update_tree(enter_i, enter_j, imp, imp_i, imp_j, P, left, right, left_parents, right_parents)
        else
            if bad_index == length(bad_i)
                bad_index += 1
                push!(bad_i, enter_i)
                push!(bad_j, enter_j)
            else
                bad_index += 1
                bad_i[bad_index] = enter_i
                bad_j[bad_index] = enter_j
            end
        end
    end
    println("Reached iteration limit")
    return P
end

# Creates random cost-matrix inplace, using i.i.d. d-dimensional Gaussian vectors
function random_cost(n,m,C;d=3)
    x_points = randn(n,d)
    y_points = randn(m, d)
    for i in 1:n
        for j in 1:m
            C[i,j] = sum((x_points[i] - y_points[j]).^2)
        end
    end
end

# Tests my_emd() over a range of synthetic inputs
function test()
    # Size of support of two measures. n corrseponds to rows and m to columns.
    ns = [3,5,10,15,29,47, 99]
    ms = [4,5,9,16,33,51,101]
    for i in 1:length(ns)
        for j in 1:length(ms)
            n = ns[i]
            m = ms[j]
            # Random points with C the n × m cost (squared distance) matrix
            C = zeros(n,m)
            random_cost(n,m,C)

            # Uniform measures on the support
            a = ones(1, n)./n
            b = ones(1, m)./m

            γ = OptimalTransport.emd(vec(a), vec(b), C)
            # @btime γ = OptimalTransport.emd(vec(a), vec(b), C);

            P = my_emd(a,b,C,α = 1)
            # @btime P = my_emd(a,b,C)
            if !isapprox(γ, P)
                println(sum(abs.(γ -P)))
                return C
            else
                println("Test passed ", (i-1)*length(ms) + j, "/", length(ns)*length(ms))
            end
        end
    end
    return true
end

# Test does not always pass. When it doesn't it is due to: gets stuck in local optima because
# non-strongly feasible entering variables are used (see Bertsekas: Network Optimization (1997) page 183)
# and algorithm reaches iteration limit
test()

###################### PERFORMANCE ANALYSIS
const to = TimerOutput()

grid = Int.(round.(exp.(log(4):0.2:log(750))))
n_average = 3
times = Array{Float64, 2}(undef, (length(grid), 2))
mem_usage = Array{Float64, 2}(undef, (length(grid), 2))
for j in 1:length(grid)
    l = length(grid)
    println("$j/$l")
    n = grid[j]
    for i in 1:n_average
        m = n
        # Random squared distance matrix
        C = zeros(n,m)
        random_cost(n,m,C)

        # Uniform measures on the support
        a = ones(1, n)./n
        b = ones(1, m)./m

        @timeit to "n = m = $n" my_emd(a,b,C, α=.1)
        @timeit to "n = m = $n, OptimalTransport.jl" OptimalTransport.emd(vec(a), vec(b), C)
    end
    times[j,:] .= [TimerOutputs.time(to["n = m = $n"])/TimerOutputs.ncalls(to["n = m = $n"]),
                  TimerOutputs.time(to["n = m = $n, OptimalTransport.jl"])/TimerOutputs.ncalls(to["n = m = $n, OptimalTransport.jl"])]
    mem_usage[j,:] .= [TimerOutputs.allocated(to["n = m = $n"])/TimerOutputs.ncalls(to["n = m = $n"]),
                      TimerOutputs.allocated(to["n = m = $n, OptimalTransport.jl"])/TimerOutputs.ncalls(to["n = m = $n, OptimalTransport.jl"])]
end


#################### BLOCK SEARCH BLOCK SIZE EXPERIMENT
αs = round.(exp.(log(0.01):.1:0), digits = 3)
n = 30
n_average = 600
α_times = []
for i in 1:length(αs)
    α = αs[i]
    l = length(αs)
    println("$i/$l")
    for _ in 1:n_average
        m = n
        # Random squared distance matrix
        C = zeros(n,m)
        random_cost(n,m,C)

        # Uniform measures on the support
        a = ones(1, n)./n
        b = ones(1, m)./m

        @timeit to "α = $α" my_emd(a, b, C, α=α)
    end
    push!(α_times, TimerOutputs.time(to["α = $α"])/TimerOutputs.ncalls(to["α = $α"]))
end



########################### PLOTTING
plot(grid, log.(times), xaxis = "n = m", yaxis = "log(nanoseconds)", title = "Running times", label = ["Ours" "C++"])
savefig("times.png")
plot(grid, log.(mem_usage./10^6), xaxis = "n = m", yaxis = "log(Gigabytes)", title = "Memory usage", label = ["Ours" "C++"])
savefig("memory.png")
plot(αs, log.(α_times), title="Block size", xaxis="α", yaxis="log(nanosecons)", label=nothing)
savefig("α.png")
