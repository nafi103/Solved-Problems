#include<bits/stdc++.h>
#define ll long long
#define frm for(int i = 0; i < m; i++)
using namespace std;
 void solution()
{
    int n,m,sH=0,c=0,x;
    cin>> n >> m;
    vector<int> v,v1;
    frm{
        cin>>x;
        v1.push_back(x);
    }
    sort(v1.begin(), v1.end());
    frm{
        if(i>0){
            v.push_back(v1[i]-v1[i-1]-1);
        }
    }
    v.push_back(v1[0]+n-v1[m-1]-1);
    sort(v.begin(), v.end(), greater<int>());
    frm{
        if(c<v[i] && v[i]-c>=3){
            sH+= v[i]-c-1;
            c+=4;
        }else if(c<v[i] && v[i]-c<=2){
            sH+= 1;
            c+=2;
        }
        else   break;
    }
    cout<<n-sH<<endl;
}
 int main(){
    int t;
    cin>>t;
    while(t--)  solution();
}