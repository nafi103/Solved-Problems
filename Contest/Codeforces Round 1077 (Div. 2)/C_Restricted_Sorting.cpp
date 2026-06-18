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
int n, arr[N], target[N];
 void solve()
{
    cin >> n;
    for(int i = 0; i < n; i++){
        cin >> arr[i];
        target[i] = arr[i];
    }
    sort(target, target + n);
    int ans = inf, mn = target[0], mx = target[n - 1];
    for(int i = 0; i < n; i++){
        if(arr[i] != target[i]){
            ans = min(ans, max(mx - arr[i], arr[i] - mn));
        }
    }
    if(ans == inf)
        cout << -1 << endl;
    else
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