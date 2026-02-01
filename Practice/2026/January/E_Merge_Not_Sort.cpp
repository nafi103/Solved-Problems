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

void solve()
{
    int n;
    cin >> n;
    int a[2 * n], id[2 * n + 1];
    for(int i = 0; i < 2 * n; i++){
        cin >> a[i];
        id[a[i]] = i;
    }
    vector<int> range;
    int r = 2 * n - 1;
    for(int i = 2 * n; i > 0 and r >= 0; i--){
        int l = id[i];
        if(l > r)
            continue;
        range.push_back(r - l + 1);
        r = l - 1;
    }
    int m = sz(range);
    reverse(all(range));
    vector<bitset<2002>> vb;
    bitset<2002> b;
    b[0] = 1;
    vb.push_back(b);
    for(auto &x: range){
        b = b | (b << x);
        vb.push_back(b);
    }
    if(vb[m][n] == 0){
        cout << -1 << endl;
        return;
    }
    vector<int> ansa, ansb;
    int j = n, p = 2 * n - 1;
    for(int i = m - 1; i >= 0; i--){
        if(j - range[i] >= 0 and vb[i][j - range[i]]){
            j-=range[i];
            while(range[i]--){
                ansa.push_back(a[p]);
                p--;
            }
        }else{
            while(range[i]--){
                ansb.push_back(a[p]);
                p--;
            }
        }
        if(j == 0)
            break;
    }
    for(p; p >= 0; p--){
        ansb.push_back(a[p]);
    }
    reverse(all(ansa));
    reverse(all(ansb));
    for(int i = 0; i < n; i++){
        cout << ansa[i] << (i == n - 1 ? "\n" : " ");
    }
    for(int i = 0; i < n; i++){
        cout << ansb[i] << (i == n - 1 ? "\n" : " ");
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