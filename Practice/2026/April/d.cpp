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
    string a, b;
    cin >> a >> b;
    vector<char> st;
    for(auto &x: a){
        if(sz(st) < 3)
            st.push_back(x);
        else{
            int m = sz(st);
            if(st[m - 3] == '(' and st[m - 2] == 'x' and st[m - 1] == 'x' and x == ')'){
                for(int i = 0; i < 3; i++){
                    st.pop_back();
                }
                st.push_back('x');
                st.push_back('x');
            }else{
                st.push_back(x);
            }
        }
    }
    vector<char> save = st;
    debug(save);
    st.clear();
    for(auto &x: b){
        if(sz(st) < 3)
            st.push_back(x);
        else{
            int m = sz(st);
            if(st[m - 3] == '(' and st[m - 2] == 'x' and st[m - 1] == 'x' and x == ')'){
                for(int i = 0; i < 3; i++){
                    st.pop_back();
                }
                st.push_back('x');
                st.push_back('x');
            }else{
                st.push_back(x);
            }
        }
    }
    debug(st)
    if(st == save){
        cout << "Yes" << endl;
    }else{
        cout << "No" << endl;
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
    cin >> t;
    for (int z = 1; z <= t; z++)
    {
        // cout<<"Case "<<z<<": ";
        solve();
    }
}