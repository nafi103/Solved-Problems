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
 int dp[201][201][201];
 int f(int one, int two, int three){
    int &ans = dp[one][two][three];
    if(ans != -1)
        return ans;
    int xr = 0;
    if(one & 1)
        xr = xr ^ 1;
    if(two & 1)
        xr = xr ^ 2;
    if(three & 1)
        xr = xr ^ 3;
    if(one)
        ans = max(ans, f(one - 1, two, three));
    if(two)
        ans = max(ans, f(one, two - 1, three));
    if(three)
        ans = max(ans, f(one, two, three - 1));
    if(xr == 0)
        ans++;
    return ans;
}
 void solve()
{
    int one, two, three, four;
    cin >> one >> two >> three >> four;
    cout << f(one, two, three) + four / 2 << endl;
}
 int32_t main()
{
    // freopen("paint.in", "r", stdin);
    // freopen("paint.out", "w", stdout);
    ios::sync_with_stdio(false), cin.tie(nullptr), cout.tie(nullptr);
    cout.precision(10);
    cout.setf(ios::fixed);
    memset(dp, -1, sizeof dp);
    dp[0][0][0] = 0;
    int t = 1;
    cin >> t;
    for (int z = 1; z <= t; z++)
    {
        // cout<<"Case "<<z<<": ";
        solve();
    }
}