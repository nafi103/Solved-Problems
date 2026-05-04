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

mt19937 rng(chrono::steady_clock::now().time_since_epoch().count());
int getRandomNumber(int l, int r) {return uniform_int_distribution<int>(l, r)(rng);} 

bool in_circle(int ox, int oy, int x, int y, int r){
    return (ox - x) * (ox - x) + (oy - y) * (oy - y) <= r * r;
}

void solve()
{
    int n, r;
    cin >> n >> r;
    vector<pair<int,int>> pt(n);
    for(auto &[x, y]: pt)
        cin >> x >> y;
    int h = ceil(sqrt(3.0) * r);
    int required = (89 * n + 99) / 100;
    debug(required)
    for(int trav = 0; trav < 200; trav++){
        int dx = getRandomNumber(0, 2 * r - 1);
        int dy = getRandomNumber(0, 2 * h - 1);
        int covered = 0;
        set<pair<int,int>> circle;

        for(auto &[x, y] : pt){
            int app_row_num = (y - dy) / h;

            for(int row_num = app_row_num - 1; row_num <= app_row_num + 1; row_num++){
                bool found = false;
                int app_col_num = (x - dx - ((row_num & 1) ? r: 0)) / (2 * r);
                for(int col_num = app_col_num - 1; col_num <= app_col_num + 1; col_num++){
                    int cx = col_num * 2 * r + ((row_num & 1) ? r: 0) + dx;
                    int cy = row_num * h + dy;

                    if(in_circle(cx, cy, x, y, r)){
                        covered++;
                        found = true;
                        circle.insert({cx, cy});
                        break;
                    }
                }
                if(found)
                    break;
            }
        }

        if(covered < required){
            continue;
        }

        cout << sz(circle) << endl;
        for(auto &[ox, oy]: circle){
            cout << ox << " " << oy << endl;
        }
        return;
    }
    cout << -1 << endl;
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