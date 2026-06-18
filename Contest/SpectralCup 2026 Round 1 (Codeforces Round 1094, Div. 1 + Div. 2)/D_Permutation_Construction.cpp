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
const int N = 2e5 + 10;
int n, arr[N], ans[N], pref[N];
pair<int,int> pos[N];
 void solve()
{
    cin >> n;
    for(int i = 0; i < n; i++){
        cin >> arr[i];
        if(i)
            pref[i] = (pref[i - 1] + arr[i - 1]);
    }
    for(int i = 0; i < n; i++){
        pos[i] = {pref[i], i};
    }
    sort(pos, pos + n);
    for(int i = n - 1, j = 0; i >= 0; i--, j++){
        ans[pos[i].second] = j + 1;
    }
    for(int i = 0; i < n; i++){
        cout << ans[i] << " \n"[i == n - 1];
    }
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