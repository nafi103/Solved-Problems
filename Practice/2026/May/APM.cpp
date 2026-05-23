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

pair<string,string> seperate(string str){
    string v1 = "", v2 = "";
    bool flag = false;
    for(auto &c: str){
        if(flag)
            v2.push_back(c);
        else if(c == ':')
            flag = true;
        else
            v1.push_back(c);
    }
    return make_pair(v1, v2);
}

void solve()
{
    map<pair<string,string>, int> id;
    map<int, pair<string, string>> package;
    set<string> packages;
    int n, cnt = 1;
    vector<vector<int>> g;
    cin >> n;
    while(n--){
        cout << "Request " << cnt++ << ": ";
        string str;
        cin >> str;
        auto [v1, v2] = seperate(str);
        int m;
        cin >> m;
        if(m){
            vector<int> dependant(m);
            bool flag = true;
            string tstr;
            for(int i = 0; i < m; i++){
                cin >> tstr;
                if(packages.count(tstr) == 0)
                    flag = false;
                if(!flag)
                    continue;
                pair<string, string> need_package = seperate(tstr);
                dependant[i] = id[need_package];
            }
            if(!flag){
                cout << "ERROR" << endl;
                continue;
            }
            vector<pair<string,string>> all_dependant;
            queue<int> q;
            vector<bool> visited(sz(g));
            for(auto &node: dependant){
                q.push(node);
                visited[node] = true;
            }

            while(!q.empty()){
                int node = q.front();
                q.pop();
                all_dependant.push_back(package[node]);
                for(auto &adj: g[node]){
                    if(!visited[adj]){
                        visited[adj] = true;
                        q.push(adj);
                    }
                }
            }

            sort(all(all_dependant));

            for(int i = 1; i < sz(all_dependant); i++){
                if(all_dependant[i - 1].first == all_dependant[i].first and
                    all_dependant[i - 1].second != all_dependant[i].second){
                    flag = false;
                    break;
                }
            }

            if(!flag){
                cout << "ERROR\n";
                continue;
            }

            cout << "OK\n";
            packages.insert(str);
            package[sz(package)] = {v1, v2};
            id[{v1, v2}] = sz(id);
            g.push_back(dependant);
            for(auto &str: packages){
                cout << str << endl;
            }
        }else{
            package[sz(package)] = {v1, v2};
            id[{v1, v2}] = sz(id);
            g.push_back(vector<int>());
            packages.insert(str);
            cout << "OK\n";
            for(auto &str: packages){
                cout << str << endl;
            }
        }
    }
}

const vector<string> codes = {".","-","..","-.",".-","...","--","-..",".-.","..-","....","--.","-.-","-...",".--",".-..","..-.","...-",".....","---","--..","-.-.","-..-","-....",".--.",".-.-",".-...","..--","..-..","...-.","....-","......","---.","--.-","--...","-.--"};

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