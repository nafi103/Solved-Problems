#include <bits/stdc++.h>

using namespace std;

/****************************************************************/

#define int long long
#define sz(x) (int)(x).size()
#define all(x) x.begin(), x.end()
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

int query(int l, int r)
{
    cout << "? " << (r - l + 1);
    for (int i = l; i <= r; i++)
    {
        cout << " " << i;
    }
    cout << endl;
    cin >> l;
    return l;
}

void solve()
{
    int n;
    cin >> n;
    if(n == 1){
        cout << "! 1 2 3" << endl;
        return;
    }
    int R = inf, L = -inf;
    int l = 1, r = 2 * n;
    while (l <= r)
    {
        int mid = (l + r) / 2;
        int x = query(1, mid);
        int rem = (mid - x);
        if (rem & 1)
        {
            R = min(R, mid);
            r = mid - 1;
        }
        else
        {
            l = mid + 1;
        }
    }
    l = 1;
    r = R - 1;
    while (l <= r)
    {
        int mid = (l + r) / 2;
        int x = query(mid, R);
        int rem = (R - mid + 1 - x);
        if (rem & 1)
        {
            L = max(L, mid);
            l = mid + 1;
        }
        else
        {
            r = mid - 1;
        }
    }
    l = L;
    r = R;
    int ans = l + 1;
    while (l <= r)
    {
        int mid = (l + r) / 2;
        int x1 = query(L, mid), x2 = query(L + 1, mid);
        if (x2 > x1)
        {
            r = mid - 1;
            ans = mid;
        }
        else
        {
            l = mid + 1;
        }
    }
    cout << "! " << L << " " << ans << " " << R << endl;
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