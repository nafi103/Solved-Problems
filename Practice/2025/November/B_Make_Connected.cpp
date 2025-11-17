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

int grid[110][110];
int n;

int dx[] = {1, 0, 0, 1, -1, 0, 0, -1};
int dy[] = {0, 1, 1, 0, 0, 1, 1, 0};

bool square()
{
    for (int i = 1; i <= n - 1; i++){
        for (int j = 1; j <= n - 1; j++){
            if(grid[i][j] and grid[i+1][j] and grid[i][j+1] and grid[i+1][j+1])
                return true;
        }
    }
    return false;
}

int check(int r, int c, int id){
    int cnt = 0;
    while(r<=n and c<=n and r>=1){
        cnt += grid[r][c];
        r += dx[id];
        c += dy[id];
        id ^= 1;
    }
    return cnt;
}

void solve()
{
    int cnt = 0;
    char tmp;
    cin >> n;
    for (int i = 1; i <= n; i++)
    {
        for (int j = 1; j <= n; j++)
        {
            cin >> tmp;
            if (tmp == '.')
                grid[i][j] = 0;
            else
            {
                grid[i][j] = 1;
                cnt++;
            }
        }
    }
    if(cnt<=1){
        cout << "YES" << endl;
        return;
    }
    if (square())
    {
        cout << (cnt == 4 ? "YES" : "NO") << endl;
        return;
    }
    int lr, lc;
    for (int j = 1,flag = true; j <= n and flag; j++){
        for (int i = 1; i <= n; i++){
            if(grid[i][j]){
                lr = i;
                lc = j;
                flag = false;
                break;
            }
        }
    }
    for (int i = 0; i < 8; i+=2){
        if(check(lr,lc,i)==cnt){
            cout << "YES" << endl;
            return;
        }
    }
    cout << "NO" << endl;
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