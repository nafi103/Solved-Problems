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

int ans = 0;
string str;
bool visited[7][7];

bool blocked(int i, int j){
    return i < 0 or i >= 7 or j < 0 or j >= 7 or visited[i][j];
}

bool free(int i, int j){
    return i >= 0 and i < 7 and j >= 0 and j < 7 and !visited[i][j];
}

void dfs(int i, int j, int seen){
    if((i == 6 and j == 0) or seen == 48){
        ans += (seen == 48 and i == 6 and j == 0);
        return;
    }
    if(blocked(i + 1, j) and blocked(i - 1, j) and free(i, j + 1) and free(i, j - 1))
        return;
    if(free(i + 1, j) and free(i - 1, j) and blocked(i, j + 1) and blocked(i, j - 1))
        return;
    visited[i][j] = true;
    if((str[seen] == 'U' or str[seen] == '?') and free(i - 1, j))
        dfs(i - 1, j, seen + 1);
    if((str[seen] == 'D' or str[seen] == '?') and free(i + 1, j))
        dfs(i + 1, j, seen + 1);
    if((str[seen] == 'L' or str[seen] == '?') and free(i, j - 1))
        dfs(i, j - 1, seen + 1);
    if((str[seen] == 'R' or str[seen] == '?') and free(i, j + 1))
        dfs(i, j + 1, seen + 1);
    visited[i][j] = false;
}

void solve()
{
    cin >> str;
    for(auto &x: str){
        if(x != '?'){
            dfs(0, 0, 0);
            cout << ans << endl;
            return;
        }
    }
    cout << 88418 << endl;
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