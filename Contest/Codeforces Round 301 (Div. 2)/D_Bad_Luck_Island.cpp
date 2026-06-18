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
    int R, S, P;
    cin >> R >> S >> P;
    double dp[R + 1][S + 1][P + 1];
    memset(dp, 0, sizeof dp);
    dp[R][S][P] = 1;
    for(int sum = R + P + S; sum > 0; sum--){
        for(int r = R; r >= 0; r--){
            for(int s = S; s >= 0; s--){
                int p = sum - r  - s;
                if(p < 0 or p > P)
                    continue;
                if(s + r + p == max({r, s, p}))
                    continue;
                double &curr = dp[r][s][p];
                int sl = r * s, rl = p * r, pl = s * p, total = rl + pl + sl;
                if(r)
                    dp[r - 1][s][p] += curr * rl / total;
                if(s)
                    dp[r][s - 1][p] += curr * sl / total;
                if(p)
                    dp[r][s][p - 1] += curr * pl / total;
            }
        }
    }
    double ansr = 0, anss = 0, ansp = 0;
    for(int i = 1; i <= R; i++)
        ansr += dp[i][0][0];
    for(int i = 1; i <= S; i++)
        anss += dp[0][i][0];
    for(int i = 1; i <= P; i++)
        ansp += dp[0][0][i];
    cout << ansr << " " << anss << " " << ansp << endl;
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