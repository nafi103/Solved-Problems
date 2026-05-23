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
const vector<string> codes = {".","-","..","-.",".-","...","--","-..",".-.","..-","....","--.","-.-","-...",".--",".-..","..-.","...-",".....","---","--..","-.-.","-..-","-....",".--.",".-.-",".-...","..--","..-..","...-.","....-","......","---.","--.-","--...","-.--"};

void solve()
{
    map<char, int> mp;
    for(char c = 'a'; c <= 'z'; c++){
        mp[c] = 0;
    }
    for(char c = '0'; c <= '9'; c++){
        mp[c] = 0;
    }

    string s;
    getline(cin, s);
    stringstream ss(s);
    string t;
    while (ss >> t) {
        for(auto &c: t){
            if (isalpha(c)) 
                c = tolower(c);
            mp[c]++;
        }
    }

    vector<pair<int,char>> arr;
    arr.reserve(36);
    for(auto &[f, s]: mp){
        arr.push_back({s, f});
    }
    sort(all(arr), [&](pair<int, char> &a, pair<int, char>& b){
        if(a.first != b.first)
            return a.first > b.first;
        return a.second > b.second;
    });

    vector<string> alp(26), num(10);
    int m = 36;
    for(int i = 0; i < m; i++){
        char c = arr[i].second;
        if(isalpha(c)){
            alp[c - 'a'] = codes[i];
        }else{
            num[c - '0'] = codes[i];
        }
    }

    for(auto &str: alp)
        cout << str << endl;
    for(auto &str: num)
        cout << str << endl;
}

int32_t main()
{
    // freopen("paint.in", "r", stdin);
    // freopen("paint.out", "w", stdout);
    ios::sync_with_stdio(false), cin.tie(nullptr), cout.tie(nullptr);
    cout.precision(10);
    cout.setf(ios::fixed);

    // vector<pair<int,string>> pcodes;
    // for(int i = 1; i <= 10; i++){
    //     for(int j = i; j >= 0; j--){
    //         if(j % 3 != 0)
    //             continue;
    //         string str = "";
    //         int dot = i - j, dash = j / 3;
    //         while(dot--)
    //             str.push_back('.');
    //         while(dash--)
    //             str.push_back('-');
    //         sort(all(str));
    //         do{
    //             pcodes.push_back({i, str});
    //         }while(next_permutation(all(str)));
    //     }
    // }
    // while(sz(pcodes) > 36)
    //     pcodes.pop_back();
    // debug(pcodes)
    // cerr << '{';
    // for(auto &[f, s]: pcodes){
    //     cerr << "\"" << s << "\"" << ",";
    // }
    // cerr << '}';

    int t = 1;
    cin >> t;
    cin.ignore();
    for (int z = 1; z <= t; z++)
    {
        // cout<<"Case "<<z<<": ";
        solve();
    }
}