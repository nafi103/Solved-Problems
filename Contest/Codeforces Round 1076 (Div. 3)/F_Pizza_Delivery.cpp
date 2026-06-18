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
    int n, x1, y1, x2, y2;
    cin >> n >> x1 >> y1 >> x2 >> y2;
    vector<int> a(n);
    for(int i = 0; i < n; i++)
        cin >> a[i];
    map<int,vector<int>> mp;
    for(int i = 0, x; i < n; i++){
        cin >> x;
        mp[a[i]].push_back(x);
    }
     for(auto &[f, s]: mp)
        sort(all(s));
    mp[x1].push_back(y1);
    mp[x2].push_back(y2);
     vector<pair<int,vector<int>>> arr;
    for(auto &[f,s]: mp)
        arr.emplace_back(f, s);
    n = sz(arr);
     vector<vector<int>> dp(2, vector<int>(n));
    dp[0][0] = 0, dp[1][0] = 0;
    for(int i = 1; i < n; i++){
        dp[0][i] = arr[i].first - arr[i - 1].first + arr[i].second.back() - arr[i].second[0] +
                    min(dp[0][i - 1] + abs(arr[i].second.back() - arr[i - 1].second[0]),
                        dp[1][i - 1] + abs(arr[i].second.back() - arr[i - 1].second.back()));
        dp[1][i] = arr[i].first - arr[i - 1].first + arr[i].second.back() - arr[i].second[0] +
                    min(dp[0][i - 1] + abs(arr[i].second[0] - arr[i - 1].second[0]),
                        dp[1][i - 1] + abs(arr[i].second[0] - arr[i - 1].second.back()));
    }
     cout << dp[0][n - 1] << endl;
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