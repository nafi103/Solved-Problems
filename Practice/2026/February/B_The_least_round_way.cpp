#include <bits/stdc++.h>

using namespace std;

/****************************************************************/

#define int long long
#define sz(x) (int)(x).size()
#define all(x) x.begin(), x.end()
#define endl "\n"
const int mod = 998244353;
const int inf = 1e9 + 10;

#ifndef ONLINE_JUDGE
#include "debug.h"
#define debug(x) cerr << "Line " << __LINE__ << ": " << #x << " = "; _print(x); cerr << endl;
#else
#define debug(...)
#endif

/****************************************************************/

int n;

pair<int,string> minimum(vector<vector<int>> &grid){
    for(int i = 0; i < n; i++){
        for(int j = 0; j < n; j++){
            if(i == 0 and j == 0)
                continue;
            if(i == 0)
                grid[i][j] += grid[i][j - 1];
            else if(j == 0)
                grid[i][j] += grid[i - 1][j];
            else
                grid[i][j] += min(grid[i - 1][j], grid[i][j - 1]);
        }
    }
    int f = grid[n - 1][n - 1];
    int r = n - 1, c = n - 1;
    string ans = "";
    while(!(r == c and r == 0)){
        if(r == 0){
            c--;
            ans.push_back('R');
        }else if(c == 0){
            r--;
            ans.push_back('D');
        }else{
            if(grid[r - 1][c] < grid[r][c - 1]){
                r--;
                ans.push_back('D');
            }else{
                c--;
                ans.push_back('R');
            }
        }
    }
    reverse(all(ans));
    return {f, ans};
}

void solve()
{
    cin >> n;
    vector<vector<int>> two(n, vector<int>(n, 0)), five(n, vector<int>(n, 0));
    bool zero_found = false;
    int xx, yy;
    for(int i = 0; i < n; i++){
        for(int j = 0; j < n; j++){
            int x, cnt = 0;
            cin >> x;
            if(x == 0){
                zero_found = true;
                xx = i;
                yy = j;
                two[i][j] = 1;
                five[i][j] = 1;
                continue;
            }
            while(x % 2 == 0){
                x /= 2;
                cnt++;
            }
            two[i][j] = cnt;
            cnt = 0;
            while(x % 5 == 0){
                x /= 5;
                cnt++;
            }
            five[i][j] = cnt;
        }
    }
    auto [t, ans1] = minimum(two);
    auto [f, ans2] = minimum(five);
    if(zero_found and min(t, f) >= 1){
        cout << 1 << endl;
        for(int i = 1; i <= xx; i++)
            cout << 'D';
        for(int j = 1; j <= yy; j++)
            cout << 'R';
        for(int i = xx + 1; i < n; i++)
            cout << 'D';
        for(int j = yy + 1; j < n; j++)
            cout << 'R';
        return;
    }
    if(t < f){
        cout << t << endl;
        cout << ans1 << endl;
    }else{
        cout << f << endl;
        cout << ans2 << endl;
    }
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