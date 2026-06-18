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
 int expo(int a, int b){
    int res = 1;
    while(b > 0){
        if(b & 1)
            res = (res * a) % mod;
        a = (a * a) % mod;
        b >>= 1;
    }
    return res;
}
 int mminvprime(int a) {
    return expo(a, mod - 2);
}
 const int N = 2e5 + 10;
int n,k,dp[N],fact[N],ifact[N];
 void input(){
    cin >> n >> k;
}
 int nCk(int a, int b){
    return ((fact[a] * ifact[b]) % mod * ifact[a - b]) % mod;
}
 void solve()
{
    input();
    if(k == 0){
        cout << 1 << endl;
        return;
    }
    if(n == 1){
        cout << expo(2, k) << endl;
        return;
    }
    int ans = 0;
    if((n & 1) == 0){
        int zero = expo(2 , n - 1) - 1;
        for(int i = k, prev_zero = 1; i > 0; i--, prev_zero = (prev_zero * zero) % mod){
            ans = (ans + (prev_zero * expo(2, (i - 1) * n)) % mod) % mod;
        }
        ans = (ans + expo(zero, k)) % mod;
    }else{
        int zero = expo(2 , n - 1);
        for(int i = 0; i <= k; i++){
            int tmp = (nCk(k, i) * expo(zero, k - i)) % mod;
            ans = (ans + tmp) % mod;
        }
    }
    cout << ans << endl;
}
 int32_t main()
{
    // freopen("paint.in", "r", stdin);
    // freopen("paint.out", "w", stdout);
    ios::sync_with_stdio(false), cin.tie(nullptr), cout.tie(nullptr);
    cout.precision(10);
    cout.setf(ios::fixed);
    int t = 1;
    cin >> t;
    fact[0] = 1;
    for(int i = 1; i < N; i++)
        fact[i] = (fact[i - 1] * i) % mod;
    ifact[N - 1] = mminvprime(fact[N - 1]);
    for(int i = N - 2; i >= 0; i--)
        ifact[i] = (ifact[i + 1] * (i + 1)) % mod;
    for (int z = 1; z <= t; z++)
    {
        // cout<<"Case "<<z<<": ";
        solve();
    }
}