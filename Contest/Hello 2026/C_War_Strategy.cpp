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
    int n, m, k, ans = 1;
    cin >> n >> m >> k;
    int a = k - 1, b = n - k;
    if(a > b)
        swap(a, b);
    for(int take = 0; take <= a; take++){
        int ta = 0;
        int tm = m - max(0ll, 2 * take - 1);
        if(tm < 0)
            break;
        ta = take + 1;
        int people = max(1ll, take);
        if(people >= tm){
            ta += min(b, tm);
        }else{
            people += (tm - people) / 2;
            ta += min(b, people);
        }
        ans = max(ans, ta);
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