using DataStructures
using OptimalTransport
using BenchmarkTools

# This function produces a basic feasible starting point in place into P and
# inputs the sparsity (tree) structure into left & right. left[i] & right[j] are BitSets,
# essentially implementing a set with fast inclusion, addition and deletion operations.
function NorthWest!(left, right, P, a, b)
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
function updatePotential!(u, v, C, left, right)
    # Since tree structure might in fact be a forest, need to start DFS from
    # an arbitrary root in each disjoint tree. We keep track of the updated
    # nodes on the left of the bipartite graph in 'unchanged'.
    unchanged = BitSet(1:n)
    while length(unchanged) > 0
        # println("Outside")
        root = last(unchanged)
        u[root] = 0
        DFS_potential!(root, 0, u, v, C, left, right, unchanged)
    end
end


# Helper for updatePotential(). side = {0,1} = {left,right}. Basically a standard DFS implementation
function DFS_potential!(node, side, u, v, C, left, right, unchanged)
    if side == 0
        # If have already visited this node, then return
        if !(node in unchanged)
            return
        end
        for neighbour in left[node]
            # println("Looking at right ", neighbour, " from left ", node, " unchanged = ", unchanged)
            v[neighbour] = C[node,neighbour] - u[node]
            delete!(unchanged, node)
            DFS_potential!(neighbour, 1, u, v, C, left, right, unchanged)
        end
    else
        for neighbour in right[node]
            # println("Looking at left ", neighbour, " from right ", node, " unchanged = ", unchanged)
            u[neighbour] = C[neighbour, node] - v[node]
            DFS_potential!(neighbour, 0, u, v, C, left, right, unchanged)
        end
    end
end


# We find the entering edge by finding the minimal difference C - u - v over
# all edges. Currently not implementing block pivoting.
function find_entering(u, v, C)
    currmin = 0
    enter_i = enter_j = -1
    for i in 1:n
        for j in 1:m
            if C[i,j] - u[i] - v[j] < currmin
                enter_i = i
                enter_j = j
                currmin = C[i,j] - u[i] - v[j]
            end
        end
    end
    if enter_i < 0
        return (-1,-1,1)
    end
    return (enter_i, enter_j, 0)
end

# Given an edge (tail, head) we find the unique cycle containing it using BFS.
# We start a BFS search starting with the edge (tail, head) and save the results
# in left_parents & right_parents. left_parents[i] is the parent of the left node i
# and right_parents[j] is the parent of the right node j.
function find_cycle(tail, head, left, right, left_parents, right_parents)
    q = Queue{Array{UInt32, 1}}()
    enqueue!(q, [head, 1])
    # side = {0,1} is {left,right} hand side respectively
    while length(q) > 0
        node, side = dequeue!(q)
        if side == 1
            for neighbour in right[node]
                # Need the next condition to avoid turning around straight away
                # ERROR HERE
                if neighbour == tail
                    # println("HERE ", right_parents[node], " ", neighbour)
                end
                if right_parents[node] != neighbour
                    # Check whether the loop has closed
                    if neighbour == tail
                        # println("Setting left_parents[", tail, "] = ", node)
                        left_parents[tail] = node
                        return
                    end
                    left_parents[neighbour] = node
                    enqueue!(q, [neighbour, 0])
                end
            end
        else
            for neighbour in left[node]
                if left_parents[node] != neighbour
                    right_parents[neighbour] = node
                    enqueue!(q, [neighbour, 1])
                end
            end
        end
    end
end

# Disregard this function
# Given left_parents, right_parents and a node i on the cycle returns a list of the
# nodes making up the cycle.
function get_cycle(i, left_parents, right_parents)
    cycle = Vector{UInt32}()
    push!(cycle, i)
    curr = left_parents[i]
    # start iteration on right side
    side = 1
    while !(curr == i && side == 0)
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
function calculate_improvement(i, j, left_parents, right_parents, P)
    curr_i = i
    curr_j = left_parents[i]
    imp = P[i,curr_j]
    imp_i = curr_i
    imp_j = curr_j
    curr_i = right_parents[curr_j]
    # println((curr_i, curr_j))

    while curr_i != i
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
    return imp, imp_i, imp_j
end



function update_tree(i, j, imp, imp_i, imp_j, P, left, right, left_parents, right_parents)
    curr_i = i
    curr_j = j
    # println((curr_i, curr_j))
    P[curr_i, curr_j] += imp
    curr_j = left_parents[curr_i]
    P[curr_i, curr_j] -= imp
    curr_i = right_parents[curr_j]
    while curr_i != i
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
function my_emd(a, b, C)
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
    for _ in 1:100
        # println(objective(P, C))
        updatePotential!(u, v, C, left, right)
        #
        # Testing wheter updatePotential works
        # println("Potential update error = ", sum(abs2, (P .!= 0).*(C - (u.+v'))))


        enter_i, enter_j, done = find_entering(u, v, C)
        # println(done)
        if done > 0
            break
        end

        # Add entering edge to tree (creating a unique cycle)
        push!(left[enter_i], enter_j)
        push!(right[enter_j], enter_i)

        right_parents[enter_j] = enter_i
        find_cycle(enter_i, enter_j, left, right, left_parents, right_parents)

        # cycle = get_cycle(enter_i, left_parents, right_parents)
        imp, imp_i, imp_j = calculate_improvement(enter_i, enter_j, left_parents, right_parents, P)

        update_tree(enter_i, enter_j, imp, imp_i, imp_j, P, left, right, left_parents, right_parents)
    end
    return P
end

# Size of support of two measures. n corrseponds to rows and m to columns.
n = 10
m = 11
# Random points with C the n × m cost (squared distance) matrix
x = randn(n)
y = randn(m)
C = (x .- y').^2

# Uniform measures on the support
a = ones(1, n)./n
b = ones(1, m)./m

γ = OptimalTransport.emd(vec(a), vec(b), C);
# @btime γ = OptimalTransport.emd(vec(a), vec(b), C);

P = my_emd(a,b,C)
# @btime P = my_emd(a,b,C)
println(isapprox(P, γ))
