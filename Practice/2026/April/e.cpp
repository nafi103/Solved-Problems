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

bool flag = false;
char dir[] = {'U', 'L', 'R', 'D'};
int x[] = {-1, 0, 0, 1};
int y[] = {0, -1, 1, 0};

void solve()
{
    int n, a, b;
    cin >> n >> a >> b;
    if(n % 2 == 1 or (a + b) % 2 == 0){
        cout << "No" << endl;
        return;
    }
    vector<vector<bool>> visited(n, vector<bool> (n, false));
    a--, b--;
    cout << "Yes" << endl;
    string ans = "";
    visited[a][b] = true;
    int r = 0, c = 0;
    visited[r][c] = true;
    for(int i = 0; i < n * n - 2; i++){
        for(int j = 0; j < 4; j++){
            int nr = r + x[j], nc = c + y[j];
            if(nr >= 0 and nr < n and nc >= 0 and nc < n and !visited[nr][nc]){
                ans.push_back(dir[j]);
                r = nr; c = nc;
                visited[r][c] = true;
                break;
            }
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