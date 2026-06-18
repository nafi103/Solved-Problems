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
#define debug(x)                                        \
    cerr << "Line " << __LINE__ << ": " << #x << " = "; \
    _print(x);                                          \
    cerr << endl;
#else
#define debug(...)
#endif
 /****************************************************************/
 void solve()
{
    int n, ans = 0, take = 0;
    cin >> n;
    vector<int> v(n), p(n);
    pbds<pair<int, int>> d;
    for (int i = 0; i < n; i++)
    {
        cin >> v[i];
        d.insert({v[i], i});
    }
    for (auto &x : p)
    {
        cin >> x;
        x--;
    }
    for (int i = 0; sz(d) >= i + 1; i++)
    {
        int id = sz(d) - 1 - i;
        int x = (*d.find_by_order(id)).first;
        if((i + 1) * x > ans){
            ans = (i + 1) * x;
            take = i + 1;
        }
        d.erase({v[p[i]], p[i]});
    }
    cout << ans << " " << take << endl;
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