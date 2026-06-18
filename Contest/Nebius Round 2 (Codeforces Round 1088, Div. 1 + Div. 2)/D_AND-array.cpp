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
 const int N = 2e5 + 10;
int fact[N], ifact[N], n, a[N], b[N];
 int expo(int a, int b){
    int res = 1;
    while(b){
        if(b & 1)
            res = (res * a) % mod;
        a = (a * a) % mod;
        b >>= 1;
    }
    return res;
}
 int nCk(int n, int k){
    return ((fact[n] * ifact[k]) % mod * ifact[n - k]) % mod;
}
 void solve()
{
    cin >> n;
    for(int i = 1; i <= n; i++)
        cin >> b[i];
    vector<pair<int,int>> bit_num; // val, how many
    int curr_val = 0, sum = 0;
    for(int i = n; i >= 1; i--){
        int extra = 0;
        for(auto &[f, s]: bit_num){
            extra = (extra + nCk(s, i) * f) % mod;
        }
        int rem = (b[i] - extra + mod) % mod;
        if(rem)
            bit_num.push_back({rem, i});
        curr_val |= rem;
        a[i] = curr_val;
    }
    for(int i = 1; i <= n; i++){
        cout << a[i] << " \n"[i == n];
    }
}
 int32_t main()
{
    // freopen("paint.in", "r", stdin);
    // freopen("paint.out", "w", stdout);
    ios::sync_with_stdio(false), cin.tie(nullptr), cout.tie(nullptr);
    cout.precision(10);
    cout.setf(ios::fixed);
     fact[0] = 1;
    for(int i = 1; i < N; i++)
        fact[i] = (fact[i - 1] * i) % mod;
    ifact[N - 1] = expo(fact[N - 1], mod - 2);
    for(int i = N - 2; i >= 0; i--)
        ifact[i] = (ifact[i + 1] * (i + 1)) % mod;
     int t = 1;
    cin >> t;
    for (int z = 1; z <= t; z++)
    {
        // cout<<"Case "<<z<<": ";
        solve();
    }
}