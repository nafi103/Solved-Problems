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
 void solve()
{
    int n, T;
    double p;
    cin >> n >> p >> T;
    double dp[T + 1][n + 1];
    memset(dp, 0, sizeof dp);
    dp[0][0] = 1;
    for(int t = 0; t < T; t++){
        for(int c = 0; c <= n; c++){
            if(c == n)
                dp[t + 1][c] += dp[t][c];
            else{
                dp[t + 1][c + 1] += dp[t][c] * p;
                dp[t + 1][c] += dp[t][c] * (1.0 - p);
            }
        }
    }
    double ev = 0;
    for(int c = 0; c <= n; c++)
        ev += c * dp[T][c];
    cout << ev << endl;
}
 int32_t main()
{
    // freopen("paint.in", "r", stdin);
    // freopen("paint.out", "w", stdout);
    ios::sync_with_stdio(false), cin.tie(nullptr), cout.tie(nullptr);
    cout.precision(10);
    cout.setf(ios::fixed);
    int t = 1;
    for (int z = 1; z <= t; z++)
    {
        // cout<<"Case "<<z<<": ";
        solve();
    }
}