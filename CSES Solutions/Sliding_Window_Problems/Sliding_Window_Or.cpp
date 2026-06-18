#include <bits/stdc++.h>

using namespace std;

/****************************************************************/

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
    int n, k, x, a, b, c;
    cin >> n >> k >> x >> a >> b >> c;
    int arr[n], pref[n], suff[n];
    arr[0] = pref[0] = x;
    for(int i = 1; i < n; i++){
        arr[i] = (1ll * arr[i - 1] * a + b) % c;
        pref[i] = arr[i];
        if(i % k)
            pref[i] |= pref[i - 1];
    }
    suff[n - 1] = arr[n - 1];
    for(int i = n - 2; i >= 0; i--){
        suff[i] = arr[i];
        if(i % k != k - 1)
            suff[i] |= suff[i + 1];
    }
    int xr = pref[k - 1];
    for(int i = k; i < n; i++){
        xr ^= (pref[i] | suff[i - k + 1]);
    }
    cout << xr << endl;
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