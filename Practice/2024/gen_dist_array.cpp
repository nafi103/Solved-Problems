// generating a random sequence of distinct elements
#include <bits/stdc++.h>
#define int long long
using namespace std;

mt19937_64 rng(chrono::steady_clock::now().time_since_epoch().count());
int rand(int l, int r) {return uniform_int_distribution<int>(l, r)(rng);}

int32_t main(int32_t argc, char* argv[]) {
    srand(atoi(argv[1])); // atoi(s) converts an array of chars to int
    int n = rand(1, 10), k = rand(1,10);
    printf("%lld %lld\n", n,k);
    set<int> used;
    for(int i = 0; i < n; ++i) {
        int x;
        do {
            x = rand(1, 10);
        } while(used.count(x));
        printf("%lld ", x);
        used.insert(x);
    }
    puts("");
}
    