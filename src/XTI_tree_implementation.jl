using BenchmarkTools
using OptimalTransport

####################### TEST CASE 1 ###########################

# parents = [0,1,7,3,6,1,6,2,7]
# thread = [2,8,4,1,7,5,9,6,3]
# rev_thread = [4,1,9,3,6,8, 5,2,7]
# succ_num = [9,2,2,1,1,6,4,1,1]
# last_succ = [4,8,4,4,5,4,4,8,9]
#
# (u,v) = (9,8)
# (p,q) = (6,7)
#
# # Correct results after step III
# parents3 = [0,1,7,3,6,1,9,2,0]
# thread3 = [2, 8, 4, 9, 1, 5, 3, 6, 7]
# rev_thread3 = [5, 1, 7, 3, 6, 8, 9, 2, 4]
# succ_num3 = [5, 2, 2, 1, 1, 2, 3, 1, 4]
# last_succ3 = [5, 8, 4, 4, 5, 5, 4, 8, 4]
#
#
# # Correct results after step IV
# parents4 = [0, 1, 7, 3, 6, 1, 9, 2, 8]
# thread4 = [2,8,4,6,1,5,3,9,7]
# rev_thread4 = [5, 1, 7, 3, 6, 4, 9, 2, 8]
# last_succ4 = [5, 4, 4, 4, 5, 5, 4, 4, 4]
# succ_num4 = [9, 6, 2, 1, 1, 2, 3, 5, 4]



############################# TEST CASE 2 ####################################

# parents = [0,1,2,2,3,3,6,7,1,9,9,11]
# thread = [9,3,6,1,4,7,8,5,11,2,12,10]
# rev_thread = [4,10,2,5,8,3,6,7,1,12,9,11]
# succ_num = [12, 7, 5, 1, 1, 3, 2, 1, 4, 1, 2, 1]
# last_succ = [4, 4, 5, 4, 5, 8, 8, 8, 10,10,12,12]
#
# (u,v) = (7,12)
# (p,q) = (2,3)
#
# parents4 = [0,1,6,2,3,7,12,7,1,9,9,11]
# thread4 = [9, 4, 5, 1, 10,3,8,6,11,2,12,7]
# rev_thread4 = [4, 10,6,2,3,8,12,7,1,5,9,11]
# succ_num4 = [12, 2, 2, 1, 1, 3, 5, 1, 9, 1, 7, 6]
# last_succ4 = [4, 4, 5, 4, 5, 5, 5, 8, 10, 10, 5, 5]

########################### TEST CASE 3 ######################################
# parents = [0,1,2,2,4,4,3,3,7,8,8,10,10,1,14,15,15,14,17]
# thread = []
#
# (u,v) = (8, 17)
# (p,q) = (3, 8)

function STEP_I(parents, thread, rev_thread, succ_num, last_succ, p, q, u, v)
    # Setting up variables to be used in this step
    y = rev_thread[q]
    t_q = succ_num[q]
    f_q = last_succ[q]
    s_f_q = thread[f_q]
    p_s_f_q = x⃰ = parents[s_f_q]
    f_q = last_succ[q]

    # Updating T-T(q)
    thread[y], rev_thread[s_f_q] = s_f_q, y

    ptr = p
    while ptr > 0
        succ_num[ptr] -= t_q
        ptr = parents[ptr]
    end

    if p_s_f_q == 0
        x⃰ = 1
    end
    ptr = p
    while ptr != x⃰
        last_succ[ptr] = y
        ptr = parents[ptr]
    end
    if p_s_f_q == 0
        last_succ[x⃰] = y
    end

    # Updating T(q)
    parents[q] = 0

    # Thread and rev_thread:
    thread[f_q], rev_thread[q] = q, f_q
end

function STEP_III(parents, thread, rev_thread, succ_num, last_succ, p, q, u, v, x₁, x₂, y₁, y₂)
    x = y₂
    t_x₂ = succ_num[x₂]
    w = last_succ[y₂]
    s_w = thread[w]
    z = thread[w]
    p_z = parents[z]
    p_x = parents[x]
    son_x = -1
    y = rev_thread[x]
    if p_x > 0
        f_p_x = last_succ[p_x]
    end

    dirty_revs = []

    while x != x₂
        if son_x > 0
            parents[x] = son_x
        end

        succ_num[p_x] = t_x₂ - succ_num[x]

        if p_z == p_x
            thread[y] = z
            thread[w] = p_x
            push!(dirty_revs, y)
            push!(dirty_revs, w)
            w = f_p_x
            z = s_w
        else
            thread[w] = p_x
            push!(dirty_revs, w)
            w = y
        end

        son_x, x = x, p_x
        p_x  = parents[x]
        y = rev_thread[x]
        p_z = parents[z]
        s_w = thread[w]
        f_p_x = p_x > 0 ? last_succ[p_x] : 0
    end
    succ_num[y₂] = t_x₂
    parents[y₂] = 0
    if y₂ != x₂
        parents[x₂] = son_x
        thread[w] = y₂
        push!(dirty_revs, w)

        x̄₂ = son_x
        if last_succ[x̄₂] == last_succ[x₂]
            last_succ[x₂] = rev_thread[x̄₂]
        end

        x = x₂
        while x != y₂
            last_succ[x] = last_succ[x₂]
            x = parents[x]
        end
        last_succ[y₂] = last_succ[x₂]
    end
    # Fix dirty revs
    for u in dirty_revs
        rev_thread[thread[u]] = u
    end
end

function STEP_IV(parents, thread, rev_thread, succ_num, last_succ, p, q, u, v, x₁, x₂, y₁, y₂)
    # Setting up variables
    dirty_revs = []
    s_y₁ = thread[y₁]
    t_y₂ = succ_num[y₂]
    p_s_y₁ = x̄ = parents[thread[y₁]]
    f_y₂ = last_succ[y₂]

    # Performing step IV
    parents[y₂] = y₁
    thread[f_y₂], rev_thread[s_y₁] = s_y₁, f_y₂
    thread[y₁], rev_thread[y₂] = y₂, y₁
    x = y₁
    while x != 0
        succ_num[x] += t_y₂
        x = parents[x]
    end

    if x̄ == 0
        x̄ = x₁
    end
    x = y₁
    while x != x̄
        last_succ[x] = f_y₂
        x = parents[x]
    end
    if p_s_y₁ == 0
        last_succ[x̄] = f_y₂
    end
end

function update(parents, thread, rev_thread, succ_num, last_succ, p, q, u, v)
    ################# STEP I #################
    STEP_I(parents, thread, rev_thread, succ_num, last_succ, p, q, u, v)

    x₁ = 1
    x₂ = q
    y₁ = v
    y₂ = u
    ################# STEP III ###############
    STEP_III(parents, thread, rev_thread, succ_num, last_succ, p, q, u, v, x₁, x₂, y₁, y₂)

    # Update the potentials of T(q). Here T(q) is rooted at y₂
    curr = y₂
    prev = y₁
    tmp = last_succ[y₂]
    while prev != tmp
        _potential[curr] = cost(curr, prev) - _potential[prev]
        prev, curr = curr, thread[curr]
    end

    ############### STEP IV #################
    STEP_IV(parents, thread, rev_thread, succ_num, last_succ, p, q, u, v, x₁, x₂, y₁, y₂)
end

# @time update(parents, thread, rev_thread, succ_num, last_succ, p, q, u, v)
# println(parents == parents4 && thread == thread4 && rev_thread == rev_thread4 && last_succ == last_succ4 && succ_num == succ_num4)


# _flow = n × m (Sparse) Matrix representing the flow.
function flow(a,b)
    return _flow[min(a,b),max(a,b)-n]
end

function cost(a, b)
    return _cost[min(a,b), max(a,b)-n]
end

function potential(a)
    tmp = a-n
    if a < n+1 && a > 0
        return _f[a]
    elseif 0 < tmp && tmp < m+1
        return _g[tmp]
    else
        throw(error("a needs to be in [n+m]"))
    end
end


function f(a)
    if a < 1 || a > n
        throw(error("a needs to be in [n]"))
    end
    return _f[a]
end

function g(a)
    tmp = a - n
    if tmp < 1 || tmp > m
        throw(error("a-n needs to be in [m]"))
    end
    return _g[tmp]
end

# Returns the two nodes between which the entering edge lies
function find_entering()
    curr_min = 0
    enter1 = enter2 = -1
    for i in 1:n
        for j in 1:m
            tmp = _cost[i,j] - _potential[i] - _potential[n+j]
            if tmp < curr_min
                curr_min = tmp
                enter1, enter2 = i,j+n
            end
        end
    end
    return enter1, enter2
end

# Input = (enter1, enter2) the edge being added and flow where flow[(i-1)*m+j] is the flow between (i,j)
function find_leaving(enter1, enter2, parents, succ_num)
    left,right = enter1, enter2
    if enter1 > enter2
        left,right = right, left
    end
    left_δ = right_δ = 1
    left_left = left_right = right_left = right_right = -1
    while left != right
        if succ_num[left] > succ_num[right]
            p_right = parents[right]
            if p_right < right
                candidate_δ = flow(p_right, right)
                if candidate_δ < right_δ
                    right_δ = candidate_δ
                    right_right = right
                    right_left = p_right
                end
            end
            right = p_right
        else
            p_left = parents[left]
            if left < p_left
                candidate_δ = flow(left, p_left)
                if candidate_δ <= left_δ
                    left_δ = candidate_δ
                    left_left = left
                    left_right = p_left
                end
            end
            left = p_left
        end
    end
    left,right = enter1, enter2
    if enter1 > enter2
        left,right = right, left
    end
    if left_δ <= right_δ
        (u,v,p,q) = (left, right, left_right, left_left)
        return left_δ, u, v, p, q
    else
        (u,v,p,q) = (right, left, right_left, right_right)
        return right_δ, u, v, p, q
    end
end

function update_flow(u,v,δ, parents, succ_num)
    left,right = u, v
    if u > v
        left,right = right, left
    end
    println("LOL Adding δ to edge ", (left, right))
    _flow[left, right - n] = δ
    while left != right
        if succ_num[left] > succ_num[right]
            p_right = parents[right]
            if p_right < right
                println("Taking δ from edge ", (p_right, right))
                _flow[p_right, right-n] -= δ
            else
                println("Adding δ to edge ", (right, p_right))
                _flow[right, p_right - n] += δ
            end
            right = p_right
        else
            p_left = parents[left]
            if left < p_left
                println("Taking δ from edge ", (left, p_left))
                _flow[left, p_left-n] -= δ
            else
                println("Adding δ to edge ", (p_left, left))
                _flow[p_left, left-n] += δ
            end
            left = p_left
        end
    end
end

n=2
m=3
_cost = (randn(2) .- randn(3)').^2
a = ones(1, n)./n
b = ones(1, m)./m
_flow = [1/3 1/6 0; 0 1/6 1/3]
# _f = [0, cost(2,4)-cost(1,4)]
# _g = [cost(1,3),cost(1,4), cost(2,5) - (cost(2,4) - cost(1,4))]
_potential = [0, cost(2,4)-cost(1,4), cost(1,3),cost(1,4), cost(2,5) - (cost(2,4) - cost(1,4))]
# println(_cost - (_potential[1:n] .+ _potential[end-m:end]'))

parents = [0,4,1,1,2]
thread = [4,5,1,2,3]
rev_thread = [3, 4, 5, 1, 2]
succ_num = [5, 2, 1, 3, 1]
last_succ = [3, 5, 3, 5, 5]

# (u,v,p,q) = (5,1,1,4)
# update(parents, thread, rev_thread, succ_num, last_succ, p, q, u, v)



@time γ = OptimalTransport.emd(vec(a), vec(b), _cost)

@time while true
    enter1, enter2 = find_entering()
    δ, u, v, p, q = find_leaving(enter1, enter2, parents, succ_num)

    if u > 0 && (u,v) != (q,p)
        update_flow(u, v, δ, parents, succ_num)
        update(parents, thread, rev_thread, succ_num, last_succ, p, q, u, v)
    else
        break
    end
end
