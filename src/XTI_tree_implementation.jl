n_plus_m = 9

parent = Vector{UInt32}(undef, n_plus_m)
thread = Vector{UInt32}(undef, n_plus_m)
rev_thread = Vector{UInt32}(undef, n_plus_m)
succ_num = Vector{UInt32}(undef, n_plus_m)
last_succ = Vector{UInt32}(undef, n_plus_m)

parent = [0,1,7,3,6,1,6,2,7]
thread = [2,8,4,1,7,5,9,6,3]
rev_thread = [4,1,9,3,6,8, 5,2,7]
succ_num = [9,2,2,1,1,6,4,1,1]
last_succ = [4,8,4,4,5,4,4,8,9]

(u,v) = (9,8)
(p,q) = (6,7)

function update()
    ######## Making T-T(q) independent (Step I)
    # Parents: no update needed

    # Thread and rev_thread:
    y = rev_thread[q]
    tmp1 = last_succ[q]
    tmp2 = thread[tmp1]
    thread[y], rev_thread[tmp2] = tmp2, y

    # succ_num:
    diff = succ_num[q]
    walker = p
    while walker > 0
        succ_num[walker] -= diff
        walker = parent[walker]
    end

    # last_succ:
    tmp1 = last_succ[q]
    tmp2 = thread[tmp1]
    tmp = x⃰ = parent[tmp2]
    if x⃰ == 0
        x⃰ = 1
    end
    walker = p
    while walker != x⃰
        last_succ[walker] = y
        walker = parent[walker]
    end
    if tmp == 0
        last_succ[1] = last_succ[y]
    end

    ####### Making T(q) independent
    # Parents:
    parent[q] = 0

    # Thread and rev_thread:
    thread[last_succ[q]], rev_thread[q] = q, last_succ[q]

    # succ_num: no update needed
    # last_succ: no update needed

    ######### Stuff above this line has been checked against the example given in the paper


    ####### Rerooting T(q) to have root u (Step III)
    x₁ = 1
    x₂ = q
    y₁ = v
    y₂ = u

    x = y₂
    t⃰_y₂ = succ_num[x₂]
    w = last_succ[y₂]
    z = thread[w]
    prev = -1
    while x != x₂
        # Updating parent
        next = parent[x]
        if prev > 0
            parent[x] = prev
        end

        # Updating succ_num
        succ_num[next] = t⃰_y₂ - succ_num[x]

        # Updating thread and rev_thread
        y = rev_thread[x]
        if parent[z] == next
            thread[y], rev_thread[z] = z, y
            thread[w], rev_thread[next] = next, w
            w = last_succ[next]
        else
            thread[w], rev_thread[next] = next, w
            w = y
        end
        prev, x = x, next
    end

    parent[x₂] = prev
    parent[y₂] = 0

    succ_num[y₂] = t⃰_y₂
    thread[w], rev_thread[y₂] = y₂, w
    if x₂ == y₂
        return
    end
    last_succ[x₂] = w
    x = x₂
    while x != y₂
        tmp = parent[x]
        last_succ[tmp] = last_succ[x₂]
        x = parent[x]
    end

    # TODO: check if up to Step III we are correct


    # Joining T-T(q) and the re-rooted T(q) along (y₁, y₂) (Step IV)
    tmp = x̄ = parent[thread[y₁]]
    if x̄ == 0
        x̄ = x₁
    end
    parent[y₂] = y₁
    tmp1= thread[y₁]
    tmp2 = last_succ[y₂]
    thread[tmp2], thread[y₁],  rev_thread[tmp1], rev_thread[y₂] = tmp1, y₂, tmp2, y₁
    ptr = y₁
    while !(ptr == 0)
        succ_num[ptr] += succ_num[y₂]
        ptr = parent[ptr]
    end
    ptr = y₁
    while ptr != x̄
        last_succ[ptr] = last_succ[y₂]
        ptr = parent[ptr]
    end
    if tmp == 0
        last_succ[x̄] = last_succ[y₂]
    end
end

update()

# Correct results after step III
parent3 = [0,1,7,3,6,1,9,2,0]
thread3 = [2, 8, 4, 9, 1, 5, 3, 6, 7]
rev_thread3 = [5, 1, 7, 3, 6, 8, 9, 2, 4]
succ_num3 = [5, 2, 2, 1, 1, 2, 3, 1, 4]
last_succ3 = [5, 8, 4, 4, 5, 5, 4, 8, 4]
# println(parent == parent3 && thread3 == thread && rev_thread3 == rev_thread && succ_num3 == succ_num && last_succ3 == last_succ)

# Correct results after step IV
parent4 = [0, 1, 7, 3, 6, 1, 9, 2, 8]
thread4 = [2,8,4,6,1,5,3,9,7]
rev_thread4 = [5, 1, 7, 3, 6, 4, 9, 2, 8]
last_succ4 = [5, 4, 4, 4, 5, 5, 4, 4, 4]
succ_num4 = [9, 6, 2, 1, 1, 2, 3, 5, 4]
println(parent == parent4 && thread4 == thread && rev_thread4 == rev_thread && succ_num4 == succ_num && last_succ4 == last_succ)
