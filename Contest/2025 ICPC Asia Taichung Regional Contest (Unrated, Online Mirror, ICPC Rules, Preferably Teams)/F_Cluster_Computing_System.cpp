#include <bits/stdc++.h>

using namespace std;

/****************************************************************/

#define int long long
#define pi acos(-1.0)
const int mod = 998244353;
#define inf 1e18 + 10
#define sz(x) (int)(x).size()
#define LSOne(x) ((x) & (-x))
#define all(x) x.begin(), x.end()
#define endl "\n"

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
    int cost = 0, g = 0, n;
    cin >> n;
    vector<int> pref(n), suff(n),v(n);
    for (int i = 0; i < n; i++){
        cin >> v[i];
        pref[i] = v[i];
        if(i)
            pref[i] = gcd(pref[i], pref[i - 1]);
    }
    for (int i = n-1; i >= 0; i--){
        suff[i] = v[i];
        if (i < n - 1)
            suff[i] = gcd(suff[i], suff[i + 1]);
    }
    for (int i = 0; i < n-1; i++){
        cost += min(pref[i], suff[i]);
    }
    cout << cost << endl;
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