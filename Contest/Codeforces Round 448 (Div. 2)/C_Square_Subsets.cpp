#include <bits/stdc++.h>
 using namespace std;
 /****************************************************************/
 #define int long long
#define sz(x) (int)(x).size()
#define all(x) x.begin(), x.end()
#define endl "\n"
const int mod = 1e9 + 7;
const int inf = 1e18 + 10;
 #ifndef ONLINE_JUDGE
#include "debug.h"
#define debug(x) cerr << "Line " << __LINE__ << ": " << #x << " = "; _print(x); cerr << endl;
#else
#define debug(...)
#endif
 /****************************************************************/
 const int N = 71;
const int R = 1 << 19;
int dp[R][2], prev_dp[R][2], take_one, odd_prime_mask[N], cnt[N], id[N];
 int expo(int a, int b){
    int res = 1;
    while(b){
        if(b & 1)
            res = (1ll * res * a) % mod;
        a = (1ll * a * a) % mod;
        b >>= 1;
    }
    return res;
}
 // int f(int i, int mask, int mt){
//     if(i == N){
//         if(mask == 0 and !mt)
//             return take_one;
//         return 0;
//     }
//     if(cnt[i] == 0)
//         return f(i + 1, mask, mt);
//     int &ans = dp[i][mask][mt];
//     if(ans != -1)
//         return ans;
//     ans = 0;
//     //take odd times
//     int new_mask = mask, odd_way = expo(2, cnt[i] - 1), positive_even_way = (odd_way - 1 + mod) % mod;
//     for(auto &p: odd_primes[i]){
//         new_mask = new_mask ^ (1 << id[p]);
//     }
//     ans = (1ll * odd_way * f(i + 1, new_mask, 0)) % mod;
//     //take even times
//     ans = (ans + (1ll * positive_even_way * f(i + 1, mask, 0)) % mod) % mod;
//     //don't take
//     ans = (ans + f(i + 1, mask, mt)) % mod;
//     return ans;
// }
 void solve()
{
    int n;
    cin >> n;
    for(int i = 0, x; i < n; i++){
        cin >> x;
        cnt[x]++;
    }
    take_one = expo(2, cnt[1]);
    prev_dp[0][0] = take_one;
    for(int i = N - 1; i >= 2; i--){
        if(cnt[i] == 0)
            continue;
        for(int mask = 0; mask < R; mask++){
            for(int mt = 0; mt < 2; mt++){
                int &ans = dp[mask][mt];
                ans = 0;
                int new_mask = mask ^ odd_prime_mask[i], odd_way = expo(2, cnt[i] - 1), positive_even_way = (odd_way - 1 + mod) % mod;
                ans = (odd_way * prev_dp[new_mask][0]) % mod;
                ans = (ans + (positive_even_way * prev_dp[mask][0])) % mod;
                ans = (ans + prev_dp[mask][mt]) % mod;
            }
        }
        swap(dp, prev_dp);
    }
    cout << (prev_dp[0][1] + take_one - 1) % mod << endl;
}
 int32_t main()
{
    // freopen("paint.in", "r", stdin);
    // freopen("paint.out", "w", stdout);
    ios::sync_with_stdio(false), cin.tie(nullptr), cout.tie(nullptr);
    cout.precision(10);
    cout.setf(ios::fixed);
     int c = 0;
    for(int i = 2; i < N; i++)
        id[i] = i;
    for(int i = 2; i < N; i++){
        if(id[i] == i){
            id[i] = c++;
            for(int j = i + i; j < N; j += i)
                id[j] = -1;
        }
    }
     for(int i = 2; i < N; i++){
        int num = i;
        for(int j = 2; j * j <= num; j++){
            if(num % j == 0){
                c = 0;
                while(num % j == 0){
                    c++;
                    num /= j;
                }
                if(c & 1)
                    odd_prime_mask[i] = (odd_prime_mask[i] | (1 << id[j]));
            }
        }
        if(num > 1)
            odd_prime_mask[i] = (odd_prime_mask[i] | (1 << id[num]));
    }
    int t = 1;
    for (int z = 1; z <= t; z++)
    {
        // cout<<"Case "<<z<<": ";
        solve();
    }
}