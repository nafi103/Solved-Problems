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
 const int N = 102;
int n, m, grid[N][N];
bool dp[N][N];
 void solve()
{
    cin >> n >> m;
    for(int i = 0; i < n; i++){
        for(int j = 0; j < m; j++)
            cin >> grid[i][j];
    }
    int mx = gcd(grid[n - 1][m - 1], grid[0][0]);
    vector<int> divisor;
    for(int i = 1; i * i <= mx; i++){
        if(mx % i == 0){
            divisor.push_back(i);
            if(i * i != mx)
                divisor.push_back(mx / i);
        }
    }
    sort(all(divisor), greater<int>());
    for(auto &target: divisor){
        for(int i = 0; i < n; i++)
            for(int j = 0; j < m; j++)
                dp[i][j] = false;
        if(dp[0][0] % target != 0 or dp[n - 1][m - 1] % target != 0)
            continue;
        dp[0][0] = true;
        for(int i = 0; i < n; i++){
            for(int j = 0; j < m; j++){
                if(grid[i][j] % target != 0)
                    continue;
                if(i)
                    dp[i][j] |= dp[i - 1][j];
                if(j)
                    dp[i][j] |= dp[i][j - 1];
            }
        }
        if(dp[n - 1][m - 1]){
            cout << target << endl;
            return;
        }
    }
    cout << 1 << endl;
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