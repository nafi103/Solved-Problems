#include <bits/stdc++.h>

using namespace std;

/****************************************************************/

#define int long long
#define sz(x) (int)(x).size()
#define all(x) x.begin(), x.end()
#define endl "\n"
const int mod = 998244353;
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
    while(b){
        if(b & 1)
            res = (res * a) % mod;
        a = (a * a) % mod;
        b >>=1;
    }
    return res;
}

const int N = 2e5 + 10;
int fact[N], ifact[N], dp[N];

int nCr(int n, int r){
    return ((fact[n] * ifact[n - r]) % mod * ifact[r]) % mod;
}

void solve()
{
    int n, m, k;
    cin >> n >> m >> k;
    int ans = 0;
    for(int i = 0; k - i * n + m - 1 >= m - 1; i++){
        int cnt = (nCr(k - i * n + m - 1, m - 1) * nCr(m, i)) % mod;
        if(i & 1)
            ans = (ans - cnt + mod) % mod;
        else
            ans = (ans + cnt) % mod;
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

    fact[0] = 1;
    for(int i = 1; i < N ; i++){
        fact[i] = (fact[i - 1] * i) % mod;
    }
    ifact[N - 1] = expo(fact[N - 1], mod - 2);
    for(int i = N - 2; i >= 0; i--){
        ifact[i] = (ifact[i + 1] * (i + 1)) % mod;
    }
    
    int t = 1;
    cin >> t;
    for (int z = 1; z <= t; z++)
    {
        // cout<<"Case "<<z<<": ";
        solve();
    }
}