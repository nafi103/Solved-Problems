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
 const int N = 2e5 + 10;
vector<vector<char>> grid(N, vector<char>(2));
int dp[N];
int n;
 int f(int i){
    if(i == n)
        return 0;
    int &ans = dp[i];
    if(ans != -1)
        return ans;
    ans = (grid[i][0] != grid[i][1]) + f(i + 1);
    if(i < n - 1){
        ans = min(ans, (grid[i][0] != grid[i + 1][0]) + (grid[i][1] != grid[i + 1][1]) + f(i + 2));
    }
    return ans;
}
 void solve()
{
    cin >> n;
    for(int i = 0; i < 2; i++){
        for(int j = 0; j < n; j++)
            cin >> grid[j][i];
    }
    for(int i = 0; i < n; i++)
        dp[i] = -1;
    cout << f(0) << endl;
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