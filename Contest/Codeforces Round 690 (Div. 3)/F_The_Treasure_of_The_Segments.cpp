#include <bits/stdc++.h>
#include <ext/pb_ds/assoc_container.hpp>
#include <ext/pb_ds/tree_policy.hpp>
 using namespace std;
using namespace chrono;
using namespace __gnu_pbds;
 template <class T>
using pbds = tree<T, null_type, less<T>, rb_tree_tag, tree_order_statistics_node_update>;
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
    int n, ans = inf;
    cin >> n;
    vector<pair<int,int>> range(n);
    for(int i = 0; i < n; i++)
        cin >> range[i].first >> range[i].second;
    sort(all(range), [&](pair<int,int> &a, pair<int,int> &b){
        if(a.second != b.second)
            return a.second < b.second;
        return a.first < b.first;
    });
    pbds<pair<int,int>> pref, suff;
    for(int i = 0; i < n; i++){
        suff.insert({range[i].first, i});
    }
    for(int i = 0; i < n; i++){
        suff.erase({range[i].first, i});
        int right = suff.order_of_key({range[i].second, inf});
        int left = sz(pref) - pref.order_of_key({range[i].first, -inf});
        ans = min(ans, n - right - left - 1);
        pref.insert({range[i].second, i});
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