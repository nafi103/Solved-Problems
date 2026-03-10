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

int ans[] = {0, 1, 2, 2, 3, 3};

void solve()
{
    int n;
    cin >> n;
    if(n < 6){
        cout << ans[n] << endl;
        for(int i = 1; i <= n; i++){
            cout << ans[i] << " ";
        }
        cout << endl;
        return;
    }
    cout << 4 << endl;
    for(int i = 1; i <= n; i++){
        cout << (i % 4) + 1 << " ";
    }
    cout << endl;
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