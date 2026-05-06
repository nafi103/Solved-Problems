#include <bits/stdc++.h>

using namespace std;

/****************************************************************/

#define xx first
#define yy second
#define int long long
#define sz(x) (int)(x).size()
#define all(x) x.begin(), x.end()
const int mod = 998244353;
const int inf = 1e18 + 10;

#ifndef ONLINE_JUDGE
#include "debug.h"
#define debug(x) cerr << "Line " << __LINE__ << ": " << #x << " = "; _print(x); cerr << endl;
#else
#define debug(...)
#endif

/****************************************************************/


const int mx = 1e9;

void solve()
{
    int n;
    cin >> n;
    pair<int,int> top_right = {-inf, -inf}, bottom_right = {-inf, inf};
    for(int i = 0, x, y; i < n; i++){
        cin >> x >> y;
        if(x + y > top_right.xx + top_right.xx){
            top_right = {x, y};
        }
        if(x - y > bottom_right.xx - bottom_right.yy){
            bottom_right = {x, y};
        }
    }
    int d1, d2;
    cout << "? R " << mx << endl;
    cin >> d1;
    cout << "? U " << mx << endl;
    cin >> d1;
    cout << "? R " << mx << endl;
    cin >> d1;
    cout << "? U " << mx << endl;
    cin >> d1;
    int x1Py1 = d1 + top_right.xx + top_right.yy;
    cout << "? D " << mx << endl;
    cin >> d2;
    cout << "? D " << mx << endl;
    cin >> d2;
    cout << "? D " << mx << endl;
    cin >> d2;
    cout << "? D " << mx << endl;
    cin >> d2;
    int x1My1 = d2 + bottom_right.xx - bottom_right.yy - 4 * mx;

    int x1 = (x1Py1 + x1My1) / 2;
    int y1 = x1Py1 - x1;

    cout << "! " << x1 - 2 * mx << " " << y1 - 2 * mx << endl;
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