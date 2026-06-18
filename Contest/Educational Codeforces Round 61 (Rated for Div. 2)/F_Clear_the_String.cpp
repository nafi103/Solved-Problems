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
 vector<vector<int>> dp;
int n;
string str;
 int f(int i, int j){
    if(i > j)
        return 0;
    if(i == j)
        return 1;
    int &ans  = dp[i][j];
    if(ans != -1)
        return ans;
    ans = 1 + f(i + 1, j);
    for(int k = i + 1; k < n; k++){
        if(str[k] == str[i]){
            ans = min(ans, f(i + 1, k - 1) + f(k, j));
        }
    }
    return ans;
}
 void solve()
{
    cin >> n;
    cin >> str;
    dp.assign(n, vector<int> (n, -1));
    cout << f(0, n - 1) << endl;
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