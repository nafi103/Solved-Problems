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
int n;

void solve()
{
    cin >> n;
    vector<int> d(n + 1, 0), dp(n + 1, 0);
    for(int i = 1; i <= n; i++){
        for(int j = i + i; j <=n; j+=i)
            d[j]++;
    }
    dp[0] = 1;
    dp[1] = 1;
    int pref = 2;
    for(int i = 2; i <= n; i++){
        dp[i] = (pref + d[i]) % mod;
        pref = (pref + dp[i]) % mod;
    }
    cout << dp[n] << endl;
}

int32_t main()
{
    // freopen("paint.in", "r", stdin);
    // freopen("paint.out", "w", stdout);
    ios::sync_with_stdio(false), cin.tie(nullptr), cout.tie(nullptr);
    cout.precision(10);
    cout.setf(ios::fixed);
    int t = 1;
    // cin >> t;
    for (int z = 1; z <= t; z++)
    {
        // cout<<"Case "<<z<<": ";
        solve();
    }
}