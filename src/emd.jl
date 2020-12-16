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
function updatePotential!(u, v, C, left, right, state, max_iter = 10000)
    n = length(u)
    m = length(v)
    # Since tree structure might in fact be a forest, need to start DFS from
    # an arbitrary root in each disjoint tree. We keep track of the updated
    # nodes on the left of the bipartite graph in 'unchanged'.
    sgn = state[1]
    for i in 1:n
        # println("Outside")
        if !(state[i] == sgn)
            continue
        end
        u[i] = 0
        DFS_potential!(i, 0, u, v, C, left, right, state, sgn)
    end
end


# Helper for updatePotential(). side = {0,1} = {left,right}. Basically a standard DFS implementation
function DFS_potential!(node, side, u, v, C, left, right, state, sgn)
    # println(unchanged)
    if side == 0
        # If have already visited this node, then return
        if state[node] != sgn
            return
        end
        state[node] = !state[node]
        for neighbour in left[node] # println("Looking at right ", neighbour, " from left ", node, " unchanged = ", unchanged) v[neighbour] = C[node,neighbour] - u[node]
            v[neighbour] = C[node,neighbour] - u[node]
            DFS_potential!(neighbour, 1, u, v, C, left, right, state, sgn)
        end
    else
        for neighbour in right[node]
            # println("Looking at left ", neighbour, " from right ", node, " unchanged = ", unchanged)
            u[neighbour] = C[neighbour, node] - v[node]
            DFS_potential!(neighbour, 0, u, v, C, left, right, state, sgn)
        end
    end
end


# We find the entering edge by finding the minimal difference C - u - v over
# all edges. Currently not implementing block pivoting.
function find_entering(u, v, C, blk_size, blk_start, res, bad_i, bad_j, bad_index)
    # println((blk_size, blk_start))
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
                # ERROR HERE
                # if neighbour == tail
                    # println("HERE ", right_parents[node], " ", neighbour)
                # end
                if right_parents[node] != neighbour
                    # Check whether the loop has closed
                    if neighbour == tail
                        # println("Setting left_parents[", tail, "] = ", node)
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

# Disregard this function
# Given left_parents, right_parents and a node i on the cycle returns a list of the
# nodes making up the cycle.
function get_cycle(i, left_parents, right_parents, max_iter = 10000)
    cycle = Vector{UInt32}()
    push!(cycle, i)
    curr = left_parents[i]
    # start iteration on right side
    side = 1
    while !(curr == i && side == 0) && max_iter > 0
        max_iter -= 1
        push!(cycle, curr)
        # println((curr, side, i, side))
        if side == 0
            curr = left_parents[curr]
        else
            curr = right_parents[curr]
        end

        side = 1 - side
    end
    return cycle
end

# Calculates the minimum value of P[i,j] along the reverse edges of the detected cycle.
function calculate_improvement(i, j, left_parents, right_parents, P, res, max_iter = 10000)
    curr_i = i
    curr_j = left_parents[i]
    imp = P[i,curr_j]
    imp_i = curr_i
    imp_j = curr_j
    curr_i = right_parents[curr_j]
    # println((curr_i, curr_j))

    while curr_i != i && max_iter > 0
        max_iter -= 1
        # println((curr_i, curr_j))
        # println("Checking edge ", (curr_i, curr_j, P[curr_i, curr_j]))
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



function update_tree(i, j, imp, imp_i, imp_j, P, left, right, left_parents, right_parents, max_iter = 10000)
    curr_i = i
    curr_j = j
    # println((curr_i, curr_j))
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


function objective(P, C)
    return vec(P)'*vec(C)
end

# runs <= 100 iterations of network simplex on measures a,b, with cost matrix C
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

    # Initializing the coupling matrix.
    P = zeros(n,m)

    # Initializing potentials
    u = zeros(n)
    v = zeros(m)

    NorthWest!(left, right, P, a, b)
    left_parents = Vector{UInt32}(undef, n)
    right_parents = Vector{UInt32}(undef, m)
    enter_i = -1
    enter_j = -1
    node_queue = Vector{UInt32}(undef, n+m)
    side_queue = Vector{Bool}(undef, n+m)

    blk_size = max(10, floor(α*m*n))
    blk_start = 1

    unchanged = Vector{Bool}(undef, n)
    fill!(unchanged, true)
    res = [0,0,0]
    res_float = [.0, .0]
    bad_i = Vector{UInt32}(undef, 20)
    bad_j = Vector{UInt32}(undef, 20)
    bad_index = 0

    while true && max_iter > 0
        max_iter -= 1
        # println(objective(P, C))
        updatePotential!(u, v, C, left, right, unchanged)
        #
        # Testing wheter updatePotential works
        # println("Potential update error = ", sum(abs2, (P .!= 0).*(C - (u.+v'))))

        prev_i = enter_i
        prev_j = enter_j
        find_entering(u, v, C, blk_size, blk_start, res, bad_i, bad_j, bad_index)
        enter_i = res[1]
        enter_j = res[2]
        done = res[3]
        blk_start += blk_size
        blk_start = (blk_start - 1)%(m*n) + 1

        if done > 0
            # println("Exited with done > 0")
            return P
        end

        # println(objective(P, C), (enter_i, enter_j))

        # Add entering edge to tree (creating a unique cycle)
        push!(left[enter_i], enter_j)
        push!(right[enter_j], enter_i)
        edges = 0
        # for i in 1:n
        #     edges += length(left[i])
        # end
        # println("Currently ", edges, "/", m + n, " edges present")

        right_parents[enter_j] = enter_i
        is_cycle = find_cycle(enter_i, enter_j, left, right, left_parents, right_parents, node_queue, side_queue)

        # cycle = get_cycle(enter_i, left_parents, right_parents)
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
    println("ran out of iterations")
    return P
end

function random_cost(n,m,C;d=3)
    x_points = randn(n,d)
    y_points = randn(m, d)
    for i in 1:n
        for j in 1:m
            C[i,j] = sum((x_points[i] - y_points[j]).^2)
        end
    end
end

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

# Performance analysis
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


plot(grid, log.(times), xaxis = "n = m", yaxis = "log(nanoseconds)", title = "Running times", label = ["Ours" "C++"])
savefig("times.png")
plot(grid, log.(mem_usage./10^6), xaxis = "n = m", yaxis = "log(Gigabytes)", title = "Memory usage", label = ["Ours" "C++"])
savefig("memory.png")
plot(αs, log.(α_times), title="Block size", xaxis="α", yaxis="log(nanosecons)", label=nothing)
savefig("α.png")

3+3
