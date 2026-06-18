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
 const int N = 1e5 + 10, M = 361;
int n, k, cnt[M], dp[M][M];
 void solve()
{
    cin >> n >> k;
    fill(cnt, cnt + k + 1, 0);
     vector<int> pos(k + 2, n);
    int mx = 0;
    for(int i = 0, x; i < n; i++){
        cin >> x;
        mx = max(mx, x);
        pos[x] = min(pos[x], i); 
    }
     for(int i = mx; i >= 0; i--){
        pos[i] = min(pos[i], pos[i + 1]);
    }
     for(int i = 0; i <= mx; i++){
        cnt[i] = n - pos[i];
    }
     for(int i = 0; i <= mx; i++){
        for(int j = 0; j <= k; j++)
            dp[i][j] = -1;
    }
     dp[0][0] = 0;
    int ans = 0;
    for(int m = 1; m <= mx; m++){
        if(cnt[m] == 0)
            continue;
        for(int used = m; used <= k; used++){
            for(int prev = 0; prev < m; prev++){
                if(dp[prev][used - m] != -1){
                    dp[m][used] = max(dp[m][used], dp[prev][used - m] + (m - prev) * cnt[m]);
                }
            }
            ans = max(ans, dp[m][used]);
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
    for (int z = 1; z <= t; z++)
    {
        // cout<<"Case "<<z<<": ";
        solve();
    }
}