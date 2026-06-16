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

const int up = 1, _right = 0;

void solve()
{
    int x, y, a, b;
    cin >> a >> b >> x >> y;

    x = abs(x), y = abs(y);
    if(a == b){
        cout << (x + y) * a << endl;
        return;
    }

    int cover = min(x, y), mn = min(a, b), mx = max(a, b);
    int cost = 2 * cover * mn;

    x -= cover;
    y -= cover;

    int dir = (mn == b);

    if(y){
        if(dir == up){

            int straight = (y + 1) / 2 * mn + (y - (y + 1) / 2) * mx;
            int another = (2 * y - (y & 1)) * mn;

            cost += min(straight, another);
        }else{
            int straight = (y + 1) / 2 * mx + (y - (y + 1) / 2) * mn;
            int another = (2 * y + (y & 1)) * mn;

            cost += min(straight, another);
        }
    }else{
        if(dir == _right){

            int straight = (x + 1) / 2 * mn + (x - (x + 1) / 2) * mx;
            int another = (2 * x - (x & 1)) * mn;

            cost += min(straight, another);
        }else{
            int straight = (x + 1) / 2 * mx + (x - (x + 1) / 2) * mn;
            int another = (2 * x + (x & 1)) * mn;

            cost += min(straight, another);
        }
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
    cin >> t;
    for (int z = 1; z <= t; z++)
    {
        // cout<<"Case "<<z<<": ";
        solve();
    }
}