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
 int nC2(int n){
    return (n * (n - 1)) / 2;
}
 void solve()
{
    int n, m, cost = 0;
    cin >> n >> m;
    vector<pair<int,int>> available;
    vector<int> dp(n + 1);
    for(int i = n; i > 1; i--){
        dp[i] = nC2(n / i);
        for(int j = i + i; j <= n; j += i)
            dp[i] -= dp[j];
        if(dp[i] / (i - 1) > 0)
            available.push_back({i - 1, dp[i] / (i - 1)});
    }
    for(auto &[d, c]: available){
        int need = m / d;
        int take = min(need, c);
        cost += (d + 1) * take;
        m -= take * d;
    }
    if(m == 0){
        cout << cost << endl;
    }else{
        cout << -1 << endl;
    }
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
    for (int z = 1; z <= t; z++)
    {
        // cout<<"Case "<<z<<": ";
        solve();
    }
}