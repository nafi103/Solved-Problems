for((i = 1; ; ++i)); do
    echo $i
    ./gen_dist_array $i > int #change name gen_array -> needed generator
    diff -w <(./D_k_Multiple_Free_Set < int) <(./brute_D < int) || break 
    #a -> file name, brute -> bruteforce solution file name
done