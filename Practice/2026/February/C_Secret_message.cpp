#include <bits/stdc++.h>

using namespace std;

/****************************************************************/

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
string str;
int n, k, ans;

void solve()
{
    ans = inf;
    cin >> n >> k;
    vector<vector<bool>> present(26, vector<bool> (n, 0));
    for(int i = 0; i < k; i++){
        cin >> str;
        for(int j = 0; j < n; j++)
            present[str[j] - 'a'][j] = true;
    }
    vector<int> div;
    for(int i = 1; i * i <= n; i++){
        if(n % i == 0){
            div.push_back(i);
            if(i * i != n)
                div.push_back(n / i);
        }
    }
    sort(all(div));
    for(auto &d: div){
        bool found = true;
        for(int i = 0; i < d; i++){
            char x = '$';
            for(int c = 0; c < 26; c++){
                bool flag = true;
                for(int j = i; j < n; j+=d){
                    if(!present[c][j]){
                        flag = false;
                        break;
                    }
                }
                if(flag){
                    x = 'a' + c;
                    break;
                }
            }
            if(x != '$')
                for(int j = i; j < n; j += d)
                    str[j] = x;
            else{
                found = false;
                break;
            }
        }
        if(found){
            cout << str << endl;
            return;
        }
    }
    cout << str << endl;
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