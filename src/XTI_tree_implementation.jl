using BenchmarkTools
using OptimalTransport
using LinearAlgebra

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
        if debug
            println("Stuck here 1")
        end
        succ_num[ptr] -= t_q
        ptr = parents[ptr]
    end

    if p_s_f_q == 0
        x⃰ = 1
    end
    ptr = p
    while ptr != x⃰
        if debug
            println("Stuck here 2")
        end
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
    t_x = succ_num[x]
    w = last_succ[y₂]
    z = thread[w]
    s_w = thread[w]
    p_z = parents[z]
    p_x = parents[x]
    son_x = -1
    y = rev_thread[x]
    if p_x > 0
        f_p_x = last_succ[p_x]
    end

    dirty_revs = []

    while x != x₂
        if debug
            println("Stuck here 3")
        end
        if son_x > 0
            parents[x] = son_x
        end
        succ_num[p_x], t_x = t_x₂ - t_x, succ_num[p_x]
        # if x == 13
        #     @printf("x = 13 p[x] = %d z = %d, y = %d w = %d p_z = %d f_p_x = %d s_w = %d", p_x,z,y,w,p_z,f_p_x,s_w)
        #     println()
        # end

        if p_z == p_x
            s_w = f_p_x
            thread[y] = z
            thread[w] = p_x
            push!(dirty_revs, y)
            push!(dirty_revs, w)
            w = f_p_x
            z = s_w
        else
            s_w = y
            thread[w] = p_x
            push!(dirty_revs, w)
            w = y
        end

        son_x, x = x, p_x
        p_x  = parents[x]
        y = rev_thread[x]
        p_z = parents[z]
        f_p_x = p_x > 0 ? last_succ[p_x] : 0
    end
    println("DFSDFSDF     ", w)
    succ_num[y₂] = t_x₂
    parents[y₂] = 0
    if y₂ != x₂
        # if last_succ[son_x] != last_succ[x]
        #     thread[x] = thread[last_succ[son_x]]
        #     thread[last_succ[x]] = y₂
        # end
        parents[x₂] = son_x
        thread[w] = y₂
        push!(dirty_revs, w)

        x̄₂ = son_x
        if last_succ[x̄₂] == last_succ[x₂]
            last_succ[x₂] = rev_thread[x̄₂]
        end

        x = x₂
        while x != y₂
            if debug
                println("Stuck here 4")
            end
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
        if debug
            println("Stuck here 5")
        end
        # println(parents)
        succ_num[x] += t_y₂
        x = parents[x]
    end

    if x̄ == 0
        x̄ = x₁
    end
    x = y₁
    while x != x̄
        if debug
            println("Stuck here + ", (y₁, x, x̄))
        end
        # if x < 1
        #     println(parents)
        #     println(thread)
        #     println(rev_thread)
        #     println(succ_num)
        #     println(last_succ)
        # end
        last_succ[x] = f_y₂
        x = parents[x]
    end
    if p_s_y₁ == 0
        last_succ[x̄] = f_y₂
    end
end

function update(parents, thread, rev_thread, succ_num, last_succ, p, q, u, v)
    # println((p,q,u,v))
    # println(parents)
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
        if debug
            println("Stuck here 8")
        end
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
    if debug
        println("Lol here ", (a, b))
    end
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
function find_entering(n, m, _cost, _potential)
    curr_min = 0
    enter1 = enter2 = -1
    for i in 1:n
        for j in 1:m
            tmp = _cost[i,j] - _potential[i] - _potential[n+j]
            if tmp < curr_min && parents[i] != j+n && parents[j+n] != i
                curr_min = tmp
                enter1, enter2 = i,j+n
            end
        end
    end
    return enter1, enter2
end

debug_enter1 = 0
debug_enter2 = 0

# Input = (enter1, enter2) the edge being added and flow where flow[(i-1)*m+j] is the flow between (i,j)
function find_leaving(enter1, enter2, parents, succ_num)
    left,right = enter1, enter2
    if enter1 > enter2
        left,right = right, left
    end
    left_δ = right_δ = 1
    left_left = left_right = right_left = right_right = -1
    while left != right
        if debug
            println("Stuck here 6")
        end
        if succ_num[left] > succ_num[right]
            p_right = parents[right]
            if p_right < right
                candidate_δ = _flow[p_right, right - n]
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
                candidate_δ = _flow[left, p_left-n]
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

function update_flow(u, v, δ, parents, succ_num)
    left,right = u, v
    if u > v
        left,right = right, left
    end
    # println("LOL Adding δ to edge ", (left, right))
    _flow[left, right - n] = δ
    while left != right
        if debug
            println("Stuck here 7")
        end
        if succ_num[left] > succ_num[right]
            p_right = parents[right]
            if p_right < right
                # println("Taking δ from edge ", (p_right, right))
                _flow[p_right, right-n] -= δ
            else
                # println("Adding δ to edge ", (right, p_right))
                _flow[right, p_right - n] += δ
            end
            right = p_right
        else
            p_left = parents[left]
            if left < p_left
                # println("Taking δ from edge ", (left, p_left))
                _flow[left, p_left-n] -= δ
            else
                # println("Adding δ to edge ", (p_left, left))
                _flow[p_left, left-n] += δ
            end
            left = p_left
        end
    end
end

function objective(P,C)
    return sum(P.*C)
end

function my_emd()
    maxiter = 100
    while maxiter > 0
        # println(maxiter)
        enter1, enter2 = find_entering(n,n,_cost, _potential)
        if enter1 < 1
            break
        end
        δ, u, v, p, q = find_leaving(enter1, enter2, parents, succ_num)
        if (u-n)*(v-n) > 0 || (p-n)*(q-n) > 0
            if debug
                println((u,v,p,q))
            end
            return
        end

        if (u,v) != (q,p)
            update_flow(u, v, δ, parents, succ_num)
            update(parents, thread, rev_thread, succ_num, last_succ, p, q, u, v)
        else
            break
        end
        maxiter -= 1
        # println(objective(_flow, _cost))
    end
end



n = 11
a = b = ones(1, n)./n
parents = vcat(0, (n+2):2n, 1, 1:(n-1))
thread = vcat((n+2):2n, n+1, 1, 2:n)
rev_thread = vcat(5, (n+2):2n, n, 1:(n-1))
succ_num = vcat(2n, (2n-2:-2:2).-1, 1, (2(n-1)):-2:2)
last_succ = vcat(5, fill(n, n-1), n+1, fill(n, n-1))

# badcost_n7 = copy(_cost)
_cost = badcost_n7
_cost = (randn(n) .- randn(n)').^2
_flow = Matrix(I(n)/n)
_potential = zeros(2n)

for i in 2:n
    _potential[i+n] = _cost[i-1, i] - _potential[i-1]
    _potential[i] = _cost[i,i] - _potential[n+i]
end
_potential[n+1] = _cost[1,1]

debug = false
@time my_emd()
println("###############################################")
@time γ = OptimalTransport.emd(vec(a), vec(b), _cost)
# # # #
println(γ == _flow)

println(parents)



enter1, enter2 = find_entering(n,n,_cost, _potential)
# if enter1 < 1
#     break
# end
δ, u, v, p, q = find_leaving(enter1, enter2, parents, succ_num)
println((δ, u, v, p, q))

# println()



if (u-n)*(v-n) > 0 || (p-n)*(q-n) > 0
    if debug
        println((u,v,p,q))
    end
end

update_flow(u, v, δ, parents, succ_num)
update(parents, thread, rev_thread, succ_num, last_succ, p, q, u, v)



println(parents)
println(thread)
println(last_succ)
println(succ_num)

STEP_I(parents, thread, rev_thread, succ_num, last_succ, p, q, u, v)
x₁ = 1
x₂ = q
y₁ = v
y₂ = u
STEP_III(parents, thread, rev_thread, succ_num, last_succ, p, q, u, v, x₁, x₂, y₁, y₂)
STEP_IV(parents, thread, rev_thread, succ_num, last_succ, p, q, u, v, x₁, x₂, y₁, y₂)


# Example that breaks
# 7×7 Array{Float64,2}:
#  3.00742   0.397879     0.0432664  1.42703     1.54062   1.78901   0.720337
#  0.310347  3.26843      1.91853    0.0003056   5.84828   6.32343   0.107831
#  5.74308   0.000992528  0.206366   3.44795     0.335169  0.455975  2.28314
#  6.31435   0.0218655    0.325631   3.89364     0.213973  0.312362  2.64834
#  0.888117  2.0237       0.999594   0.162242    4.13313   4.53405   0.00324159
#  0.279257  3.3728       1.99869    0.00012451  5.98762   6.46829   0.127461
#  0.474225  2.81008      1.57141    0.0222109   5.22932   5.67912   0.0387401
