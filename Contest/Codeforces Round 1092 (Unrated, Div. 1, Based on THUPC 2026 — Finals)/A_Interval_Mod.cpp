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
    int n, k, p, q;
    cin >> n >> k >> p >> q;
     vector<int> arr(n), mnPref(n), pq(n), qp(n);
    for(int i = 0; i < n; i++){
        cin >> arr[i];
         int x = (arr[i] % p) % q, y = (arr[i] % q) % p;
        mnPref[i] = min(x, y);
        pq[i] = x;
        qp[i] = y;
         if(i){
            mnPref[i] += mnPref[i - 1];
            pq[i] += pq[i - 1];
            qp[i] += qp[i - 1];
        }
    }
     auto get_sum = [&](int l, int r, vector<int> &pref){
        if(l > r)
            return 0ll;
        return (r < n ? pref[r]: 0) - (l ? pref[l - 1]: 0);
    };
     int ans = inf;
    for(int l = 0; l + k - 1 < n; l++){
        int r = (l + k - 1);
         ans = min(ans, min(get_sum(l, r, pq), get_sum(l, r, qp))
            + get_sum(0, l - 1, mnPref) + get_sum(r + 1, n - 1, mnPref));
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