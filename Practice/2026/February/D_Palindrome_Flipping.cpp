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

const int N = 100;
int n;
vector<int> s(N), t(N);

void make_all_equal(vector<int> &str, vector<pair<int,int>> &path){
    int id = -1;
    for(int i = 0; i < n - 1; i++){
        if(str[i] == str[i + 1]){
            id = i;
            break;
        }
    }
    if(id == -1){
        for(int i = 1; i < 4; i++){
            str[i] = str[i] ^ 1;
        }
        path.emplace_back(2, 4);
        id = 0;
    }
    int curr = str[id];
    for(int i = id + 2; i < n; i++){
        if(str[i] != curr){
            curr = curr ^ 1;
            path.emplace_back(id + 1, i);
        }
    }
    for(int i = id - 1; i >= 0; i--){
        if(str[i] != curr){
            curr = curr ^ 1;
            path.emplace_back(i + 2, n);
        }
    }
    for(int i = 0; i < n; i++)
        str[i] = curr;
}

void input(){
    char x;
    cin >> n;
    for(int i = 0; i < n; i++){
        cin >> x;
        s[i] = x - '0';
    }
    for(int i = 0; i < n; i++){
        cin >> x;
        t[i] = x - '0';
    }
}

void solve()
{
    input();
    vector<pair<int,int>> path1, path2;
    make_all_equal(s, path1);
    make_all_equal(t, path2);
    if(s[0] != t[0]){
        path1.push_back({1, n});
    }
    reverse(all(path2));
    cout << sz(path1) + sz(path2) << endl;
    for(auto &[l, r]: path1)
        cout << l << " " << r << endl;
    for(auto &[l, r]: path2)
        cout << l << " " << r << endl;
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