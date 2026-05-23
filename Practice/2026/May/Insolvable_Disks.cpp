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
    int n, ans = 0;
    cin >> n;
    vector<int> x(n), l(n), r(n);
    for(int i = 0; i < n; i++)
        cin >> x[i];

    if(n == 1){
        cout << 0 << endl;
        return;
    }

    l[0] = 0; r[0] = x[1] - x[0];
    for(int i = 1; i < n; i++){
        int dl = x[i] - x[i - 1], dr = (i + 1 == n ? inf: x[i + 1] - x[i]);
        r[i] = dl - l[i - 1]; l[i] = dl - r[i - 1];
        r[i] = min(r[i], dr);
        if(l[i] < r[i])
            ans++;
        else{
            l[i] = 0; r[i] = dr;
        }
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